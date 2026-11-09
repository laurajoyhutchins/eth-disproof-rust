from __future__ import annotations

from collections import OrderedDict
from ..runtime.cache import SharedCacheBudget, defaultdict
from collections.abc import Mapping
from dataclasses import dataclass, fields
from types import MappingProxyType
from typing import TYPE_CHECKING, Any, Protocol, cast
from time import perf_counter_ns
from sys import getsizeof

from ..core.algebra import v2
from ..core.jets import JetRing
from ..core.lazy_coefficients import NestedCoords
from ..core.network import TensorRing
from ..core.packing import Packing
from ..runtime.cost_ledger import charge, native_call

if TYPE_CHECKING:
    from ..core.modes import Mode
    from ..core.network import Network
    from ..runtime.work_trace import WorkTrace

_MEMO_MISSING = object()

class PacketRing(Protocol):
    """Deliberately dynamic coefficient ABI: Padic, jets, or expression DAG."""
    e: int
    p: int
    @property
    def zero(self) -> Any: ...
    @property
    def one(self) -> Any: ...
    def scalar(self, n: int) -> Any: ...
    def add(self, a: Any, b: Any) -> Any: ...
    def sub(self, a: Any, b: Any) -> Any: ...
    def neg(self, a: Any) -> Any: ...
    def mul(self, a: Any, b: Any) -> Any: ...
    def inv(self, a: Any) -> Any: ...
    def pow(self, a: Any, n: int) -> Any: ...


def _cauchy_unit_factors(
    t: int, z: Any, ring: PacketRing, L: int,
) -> tuple[Any, dict[int, Any]]:
    """Factor the Cauchy numerator into 2-adically integral units.

    For each q != t, factor (t - q + alpha*z) into its 2-adic
    valuation and unit part. The product denominator has the *same*
    valuation removed; only its odd part is inverted in the ring.
    """
    alpha = 1 << L.bit_length()
    denominator = 1
    for q in range(-L, L):
        if q:
            denominator *= -q
    odd_denominator = denominator >> v2(denominator)
    inverse_denominator = ring.inv(ring.scalar(odd_denominator))

    factors = {}
    for q in range(-L, L):
        if q == t:
            continue
        difference = t - q
        valuation = v2(difference)
        factors[q] = ring.add(
            ring.scalar(difference >> valuation),
            ring.mul(ring.scalar(alpha >> valuation), z),
        )
    return inverse_denominator, factors


def cauchy_values(t: int, z: Any, R: PacketRing, L: int) -> dict[int, Any]:
    """Exact Cauchy weights W_delta(t + alpha*z), alpha = 2L.

    Integer powers of two are factored out *before* inversion. The
    denominator therefore remains a 2-adic unit even for composite modulus.
    """
    a = L.bit_length() - 1
    inverse_denominator, factors = _cauchy_unit_factors(t, z, R, L)
    # Four weights are cheaper to construct directly. The linear-product
    # setup has a measurable fixed cost on the recursive L=2 hot path.
    if L == 2:
        weights: dict[int, Any] = {}
        for delta in range(-L, L):
            weight = inverse_denominator
            for q, factor in factors.items():
                if q != delta:
                    weight = R.mul(weight, factor)
            if delta != t:
                valuation = v2(t - delta)
                weight = R.mul(
                    weight, R.mul(R.scalar(1 << (a + 1 - valuation)), z),
                )
            weights[delta] = weight
        return weights

    # Every W_delta omits precisely one factor from the same numerator.
    # Prefix/suffix products avoid quadratic recomputation and never divide
    # by a potentially nonunit (or zero) factor.
    prefix: dict[int, Any] = {}
    left = R.one
    for delta in range(-L, L):
        prefix[delta] = left
        if delta != t:
            left = R.mul(left, factors[delta])

    suffix = R.one
    reversed_weights: dict[int, Any] = {}
    for delta in range(L - 1, -L - 1, -1):
        weight = R.mul(inverse_denominator, R.mul(prefix[delta], suffix))
        if delta != t:
            valuation = v2(t - delta)
            weight = R.mul(
                weight,
                R.mul(R.scalar(1 << (a + 1 - valuation)), z),
            )
            suffix = R.mul(factors[delta], suffix)
        reversed_weights[delta] = weight
    return {delta: reversed_weights[delta] for delta in range(-L, L)}


def _cross_mode_from_product(
    t: int, z: Any, R: PacketRing, L: int,
    x: int, y0: int, b: int, numerator: Any,
) -> Any:
    """Use the center's shared normalized Cauchy numerator."""
    a = L.bit_length() - 1
    alpha = 1 << (a + 1)
    center_valuation = v2(t)
    displacement = t - y0 + x
    valuation = v2(displacement)
    if valuation > center_valuation:
        raise AssertionError('Cross-group denominator must have v2 <= i')

    unit = R.add(
        R.scalar(displacement >> valuation),
        R.mul(R.scalar(alpha >> valuation), z),
    )
    inverse_unit = R.inv(unit)
    base = R.mul(
        R.mul(R.scalar(1 << (a + 1 - valuation)), z),
        R.mul(numerator, inverse_unit),
    )
    ratio = R.mul(R.scalar(1 << (center_valuation + 1 - valuation)), inverse_unit)
    return R.mul(base, R.pow(ratio, b))


def cross_mode_coefficient(
    t: int, z: Any, R: PacketRing, L: int,
    x: int, y0: int, b: int,
) -> Any:
    """Standalone exact coefficient; center-local callers reuse the product."""
    inverse_denominator, factors = _cauchy_unit_factors(t, z, R, L)
    numerator = inverse_denominator
    for factor in factors.values():
        numerator = R.mul(numerator, factor)
    return _cross_mode_from_product(t, z, R, L, x, y0, b, numerator)


class BoundedPacketMemo:
    """A center-local LRU of evaluated packet entries, bounded in two units.

    The byte estimate is deliberately conservative; the cache never retains
    values from another interpolation center or coefficient precision.
    """

    def __init__(
        self, ring: TensorRing, entries: int, max_bytes: int,
        *, shared: SharedCacheBudget | None = None,
    ) -> None:
        coordinates = ring.e
        nested: TensorRing = ring
        while isinstance(nested, JetRing):
            coordinates *= nested.q
            nested = cast(TensorRing, nested.base)
        self.entry_bytes = max(1, coordinates) * ((ring.p + 7) // 8 + 40) + 128
        self.max_bytes = max_bytes
        self.max_entries = entries if self.entry_bytes <= max_bytes else 0
        self.shared = shared
        self._owner = object()
        self.skipped_shared_budget = 0
        self._values: OrderedDict[tuple[object, ...], NestedCoords] = OrderedDict()
        self.live_bytes = 0
        self.peak_bytes = 0
        self.hits = 0
        self.misses = 0
        self.evictions = 0

    def get(self, key: tuple[object, ...]) -> NestedCoords | object:
        value = self._values.get(key, _MEMO_MISSING)
        if value is _MEMO_MISSING:
            self.misses += 1
        else:
            self._values.move_to_end(key)
            self.hits += 1
        return value

    def put(self, key: tuple[object, ...], value: NestedCoords) -> None:
        if self.max_entries == 0:
            return
        while self._values and (
            len(self._values) >= self.max_entries
            or self.live_bytes + self.entry_bytes > self.max_bytes
        ):
            self._values.popitem(last=False)
            self.live_bytes -= self.entry_bytes
            self.evictions += 1
        if self.shared is not None and not self.shared.try_set(
            self._owner, self.live_bytes + self.entry_bytes
        ):
            self.shared.try_set(self._owner, self.live_bytes)
            self.skipped_shared_budget += 1
            return
        self._values[key] = value
        self.live_bytes += self.entry_bytes
        self.peak_bytes = max(self.peak_bytes, self.live_bytes)

    def clear(self) -> None:
        self._values.clear()
        self.live_bytes = 0
        if self.shared is not None:
            self.shared.release(self._owner)


def _prepared_owned_bytes(key: tuple[object, ...], entry: PacketEntry) -> int:
    """Estimate cache-owned Python bytes, excluding shared ring/geometry/context.

    Counts keys, prepared mode terms, native argument tuples, and LRU overhead.
    It does *not* claim to measure process RSS or all transitively retained
    shared objects; use tracemalloc for observed peak allocations.
    """
    seen: set[int] = set()

    def size(obj: object) -> int:
        identity = id(obj)
        if identity in seen:
            return 0
        seen.add(identity)
        total = getsizeof(obj)
        if isinstance(obj, (tuple, list, dict, MappingProxyType)):
            if isinstance(obj, (dict, MappingProxyType)):
                for member, value in obj.items():
                    total += size(member) + size(value)
            else:
                total += sum(size(member) for member in obj)
        elif isinstance(obj, (PacketModeTerms, NativePacketTerms)):
            total += sum(size(getattr(obj, field.name)) for field in fields(obj))
        # Modes and coefficient-ring objects are referenced by existing
        # per-center structures. They are not owned by the LRU.
        return total

    # A generous fixed allowance for one OrderedDict slot and Python refs.
    return 256 + size(key) + size(entry) + size(entry.terms) + size(entry._memo_signature) + size(entry.native)


class PreparedPacketCache:
    """Center-local LRU bounded by count and estimated owned Python bytes.

    Topology, ring and mode objects are shared with the current center, not
    owned by the LRU. Every retained entry is accounted before insertion.
    """

    def __init__(
        self, limit: int, max_bytes: int = 8*1024*1024, *,
        shared: SharedCacheBudget | None = None,
    ) -> None:
        if limit < 0 or max_bytes < 1:
            raise ValueError('Prepared packet cache limits must be positive')
        self.limit = limit
        self.max_bytes = max_bytes
        self.shared = shared
        self._owner = object()
        self.skipped_shared_budget = 0
        self.values: OrderedDict[tuple[object, ...], PacketEntry] = OrderedDict()
        self.sizes: dict[tuple[object, ...], int] = {}
        self.live_bytes = 0
        self.peak_bytes = 0
        self.hits = 0
        self.misses = 0
        self.evictions = 0
        self.skipped_oversize = 0
        self.peak_entries = 0

    def get(self, key: tuple[object, ...]) -> PacketEntry | None:
        value = self.values.get(key)
        if value is None:
            self.misses += 1
        else:
            self.hits += 1
            self.values.move_to_end(key)
        return value

    def put(self, key: tuple[object, ...], value: PacketEntry) -> None:
        if self.limit == 0:
            return
        estimated = _prepared_owned_bytes(key, value)
        if estimated > self.max_bytes:
            self.skipped_oversize += 1
            return
        if key in self.values:
            del self.values[key]
            self.live_bytes -= self.sizes.pop(key)
        while self.values and (len(self.values) >= self.limit or
                               self.live_bytes + estimated > self.max_bytes):
            expired, _ = self.values.popitem(last=False)
            self.live_bytes -= self.sizes.pop(expired)
            self.evictions += 1
        if self.shared is not None and not self.shared.try_set(
            self._owner, self.live_bytes + estimated
        ):
            self.shared.try_set(self._owner, self.live_bytes)
            self.skipped_shared_budget += 1
            return
        self.values[key] = value
        self.sizes[key] = estimated
        self.live_bytes += estimated
        self.peak_bytes = max(self.peak_bytes, self.live_bytes)
        self.peak_entries = max(self.peak_entries, len(self.values))

    def clear(self) -> None:
        self.values.clear()
        self.sizes.clear()
        self.live_bytes = 0
        if self.shared is not None:
            self.shared.release(self._owner)


class EvaluationContext:
    """Arithmetic and bounded memoization shared at exactly one (t, z) center."""

    def __init__(self, t: int, z: NestedCoords, R: TensorRing, a: int, *,
                 packet_coeff_cache_limit: int | None = None,
                 packet_coeff_node_limit: int = 250_000,
                 packet_coeff_miss_limit: int = 2_000_000,
                 packet_checkpoint_coordinates: int = 0, native_packet: bool = False,
                 packet_memo_entries: int = 0, packet_memo_bytes: int = 1024*1024,
                 prepared_packet_entries: int = 0,
                 prepared_packet_bytes: int = 8*1024*1024,
                 shared_cache: SharedCacheBudget | None = None,
                 work_trace: WorkTrace | None = None) -> None:
        self.lazy_ring: LazyPacketJet | None = None
        working_ring = cast(PacketRing, R)
        work_z: Any = z
        if packet_coeff_cache_limit is not None:
            from ..core.packet_lazy import LazyPacketJet
            if not isinstance(R, JetRing):
                raise TypeError('Lazy packet coefficients require a JetRing')
            lazy_ring = LazyPacketJet(
                R, packet_coeff_cache_limit,
                node_limit=packet_coeff_node_limit,
                miss_limit=packet_coeff_miss_limit,
                checkpoint_coordinates=packet_checkpoint_coordinates,
            )
            self.lazy_ring = lazy_ring
            work_z = lazy_ring.from_dense(cast(tuple[NestedCoords, ...], z))
            working_ring = cast(PacketRing, lazy_ring)
        self.work_trace = work_trace
        # No caching of expression-DAG oracles: their representation may be
        # affected by materialization, even within a deformation center.
        self.prepared_packets = (
            PreparedPacketCache(prepared_packet_entries, prepared_packet_bytes,
                                shared=shared_cache)
            if prepared_packet_entries and self.lazy_ring is None else None
        )
        self.t = t
        self.z = work_z
        self.R = working_ring
        self.L = 1 << a
        self.native_packet = native_packet
        # No cache is created in a lazy-expression context. Results must not
        # outlive the coefficient representation that produced them.
        memo = (BoundedPacketMemo(R, packet_memo_entries, packet_memo_bytes,
                                  shared=shared_cache)
                if packet_memo_entries and not hasattr(R, 'materialize') else None)
        self.memo = memo if memo is not None and memo.max_entries else None
        self.cauchy = cauchy_values(t, work_z, working_ring, self.L)
        if self.lazy_ring is not None:
            self.cauchy = {
                delta: self.lazy_ring.checkpoint(value)
                for delta, value in self.cauchy.items()
            }
        # W_t is exactly the full normalized Cauchy product. Reusing it
        # removes one complete factorization per distinct cross coefficient.
        if -self.L <= t < self.L:
            self._cauchy_product = self.cauchy[t]
        else:
            # The public context can be constructed outside algorithmic centers.
            denominator, factors = _cauchy_unit_factors(t, work_z, working_ring, self.L)
            numerator = denominator
            for factor in factors.values():
                numerator = working_ring.mul(numerator, factor)
            self._cauchy_product = numerator
        self.cross: dict[tuple[int, int, int], Any] = {}

    def cross_coefficient(self, x: int, y0: int, b: int) -> Any:
        key = (x, y0, b)
        if key not in self.cross:
            value = _cross_mode_from_product(
                self.t, self.z, self.R, self.L, x, y0, b, self._cauchy_product,
            )
            self.cross[key] = (self.lazy_ring.checkpoint(value)
                               if self.lazy_ring is not None else value)
        return self.cross[key]


@dataclass(frozen=True)
class PacketGeometry:
    """Mode- and precision-independent packet information for one child.

    Compiled once per group/component instead of recomputing parent owners,
    slot indexes and bit positions for every weighted mode assignment.
    """
    port_map: Mapping[tuple[str, int], int]
    rows: tuple[int, ...]
    left_positions: tuple[tuple[int, int], ...]
    right_positions: tuple[tuple[int, int], ...]
    # (row slot, left bit index, ((right bit index, displacement), ...))
    # in original packet-slot order. Independent of mode and coefficients.
    row_terms: tuple[tuple[int, int, tuple[tuple[int, int], ...]], ...]
    slot_for_edge: Mapping[int, int]

    def __post_init__(self) -> None:
        # Frozen dataclasses do not freeze their dictionaries. These maps are
        # shared by sibling child contractions and must not change under them.
        object.__setattr__(self, "port_map", MappingProxyType(dict(self.port_map)))
        object.__setattr__(self, "slot_for_edge", MappingProxyType(dict(self.slot_for_edge)))


def prepare_packet_geometry(packing: Packing, packet_id: int,
                            group: int, coordinate: int,
                            port_map: Mapping[tuple[str, int], int],
                            left_owner: Mapping[int, int]) -> PacketGeometry:
    packet = packing.packets[packet_id]
    rows = tuple(slot for slot, edge in enumerate(packet.slots)
                 if edge is not None
                 and packing.groups_left[left_owner[edge]][coordinate] == group)
    right_positions = tuple(sorted((slot, bit) for (side, slot), bit
                                   in port_map.items() if side == 'X'))
    return PacketGeometry(
        port_map=port_map,
        rows=rows,
        left_positions=tuple((slot, bit) for (side, slot), bit in port_map.items()
                             if side == 'Y'),
        right_positions=right_positions,
        row_terms=tuple((x, port_map[('Y', x)],
                         tuple((bit, y - x) for y, bit in right_positions))
                        for x in rows),
        slot_for_edge={edge: slot for slot, edge in enumerate(packet.slots)
                       if edge is not None},
    )

@dataclass(frozen=True)
class PacketModeTerms:
    """Coefficient-dependent terms for one packet and mode assignment.

    Geometry is shared across assignments; these values are not. Keeping the
    two separate makes the Python and native evaluation paths consume the
    same mathematical terms.
    """
    active: tuple[tuple[Mode, int], ...]
    target: tuple[tuple[Mode, int], ...]
    source: tuple[tuple[Mode, int], ...]
    desired: tuple[int, ...]
    contributions: Mapping[int, tuple[tuple[int, Any], ...]]
    tile_slots: tuple[tuple[Mode, int, tuple[tuple[int, int], ...]], ...]
    tile_bits: tuple[tuple[Mode, int, tuple[tuple[int, int], ...]], ...]


def prepare_packet_terms(
    geometry: PacketGeometry,
    *,
    packet_id: int,
    group: int,
    t: int,
    z: NestedCoords,
    ring: TensorRing,
    packing: Packing,
    modes: list[Mode],
    multiplicities: tuple[int, ...],
    context: EvaluationContext | None,
    rows: tuple[int, ...],
) -> PacketModeTerms:
    """Prepare mode-dependent coefficients without modifying packet geometry."""
    if len(modes) != len(multiplicities):
        raise ValueError("Packet terms require one multiplicity per mode")
    active = tuple((m, b) for m, b in zip(modes, multiplicities)
                   if m.packet == packet_id and b > 0)
    target = tuple((m, b) for m, b in active if m.target == group)
    source = tuple((m, b) for m, b in active if m.source == group)
    index = {id(m): j for j, (m, _) in enumerate(target)}
    coefficients: dict[int, tuple[tuple[int, Any], ...]] = {}
    for row in rows:
        values = []
        for mode, _ in target:
            if row not in mode.rows:
                continue
            coefficient = (
                context.cross_coefficient(row, mode.y0, mode.b)
                if context is not None else
                cross_mode_coefficient(t, z, cast(PacketRing, ring),
                                       1 << packing.a, row, mode.y0, mode.b)
            )
            values.append((index[id(mode)], coefficient))
        coefficients[row] = tuple(values)

    slots = tuple((mode, b, tuple((geometry.slot_for_edge[edge], j)
                                  for edge, j in mode.tile))
                  for mode, b in source)
    bits = tuple((mode, b, tuple((position, j) for edge, j in mode.tile
                                 if (position := geometry.port_map.get(
                                     ('X', geometry.slot_for_edge[edge]))) is not None))
                 for mode, b in source)
    return PacketModeTerms(
        active=active,
        target=target,
        source=source,
        desired=tuple(b for _, b in target),
        contributions=MappingProxyType(coefficients),
        tile_slots=slots,
        tile_bits=bits,
    )


@dataclass(frozen=True, slots=True)
class NativePacketTerms:
    """Positional packet data accepted by the optional Cython kernel."""

    left_positions: tuple[int, ...]
    row_cauchy: tuple[tuple[tuple[int, Any], ...], ...]
    contributions: tuple[tuple[tuple[int, Any], ...], ...]
    right_positions: tuple[tuple[int, int], ...]


class PacketEntry:
    """Implicit packet tensor, canonically lifted from its creation modulus.

    Geometry and coefficients are prepared once. Each call only evaluates a
    bit assignment, then memoizes (when permitted) or lifts the exact result.
    """

    def __init__(self, source: Network, packing: Packing, packet_id: int,
                 g: int, i: int, t: int, z: NestedCoords,
                 create_ring: TensorRing, modes: list[Mode], beta: tuple[int, ...],
                 port_map: Mapping[tuple[str, int], int],
                 context: EvaluationContext | None = None,
                 prepared_rows: tuple[int, ...] | None = None,
                 *, geometry: PacketGeometry | None = None) -> None:
        if geometry is None:
            left_owner = {edge: j for j, vertex in enumerate(source.left)
                          for edge in vertex.ports}
            geometry = prepare_packet_geometry(
                packing, packet_id, g, i, port_map, left_owner,
            )
        self.packet_id = packet_id
        self.geometry = geometry
        self.rows = geometry.rows if prepared_rows is None else prepared_rows
        self.R = create_ring  # The fixed modulus from which values are lifted.
        self.context = context
        self.work_ring: PacketRing = (context.R if context is not None
                                      else cast(PacketRing, create_ring))
        self.terms = prepare_packet_terms(
            geometry, packet_id=packet_id, group=g, t=t, z=z,
            ring=create_ring, packing=packing, modes=modes,
            multiplicities=beta, context=context, rows=self.rows,
        )
        self.cauchy = (context.cauchy if context is not None else
                       cauchy_values(t, z, self.work_ring, 1 << packing.a))
        # Modes have identity within one center. The signature cannot be reused
        # across centers, so an object-id key here is intentional and bounded.
        self._memo_signature = (
            packet_id, g, i,
            tuple((id(mode), multiplicity) for mode, multiplicity in self.terms.active),
            tuple(sorted(geometry.port_map.items())),
        )
        self.native: NativePacketTerms | None = None
        if context is not None and context.native_packet:
            right = geometry.right_positions
            self.native = NativePacketTerms(
                left_positions=tuple(geometry.port_map['Y', row] for row in self.rows),
                row_cauchy=tuple(
                    tuple((slot, self.cauchy[slot-row]) for slot, _ in right)
                    for row in self.rows
                ),
                contributions=tuple(self.terms.contributions[row] for row in self.rows),
                right_positions=right,
            )

    def __call__(self, bits: tuple[int, ...], R: TensorRing) -> NestedCoords:
        trace = self.context.work_trace if self.context is not None else None
        started = perf_counter_ns() if trace is not None else 0
        charge('packet_entry_evaluations')
        assignment = tuple(bits)
        memo = (self.context.memo if self.context is not None and R is self.R
                else None)
        if memo is not None:
            memo_key = (self._memo_signature, assignment)
            cached = memo.get(memo_key)
            if cached is not _MEMO_MISSING:
                output = cast(NestedCoords, cached)
                if trace is not None:
                    trace.observe(
                        operation="packet", topology=self.geometry.row_terms,
                        exact_input=(id(self), assignment, id(R)),
                        started_ns=started, output=output, cache_hit=True,
                    )
                return output

        result = (self._evaluate_native(assignment) if self.native is not None
                  else self._evaluate_python(assignment))
        if self.context is not None and self.context.lazy_ring is not None:
            from ..core.lazy_coefficients import Expression
            result = self.context.lazy_ring.materialize(
                cast(Expression[NestedCoords], result),
            )
        if R is self.R:
            if memo is not None:
                memo.put((self._memo_signature, assignment), cast(NestedCoords, result))
            output = cast(NestedCoords, result)
        else:
            from ..core.jets import embed_element
            output = embed_element(cast(NestedCoords, result), self.R, R)
        if trace is not None:
            trace.observe(
                operation="packet", topology=self.geometry.row_terms,
                exact_input=(id(self), assignment, id(R)),
                started_ns=started, output=output,
            )
        return output

    def _evaluate_native(self, bits: tuple[int, ...]) -> Any:
        native = self.native
        assert native is not None
        native_call('native_packet_evaluation')
        try:
            import native_recursive
        except ImportError as exc:
            raise RuntimeError(
                'native_packet requested without native_recursive extension',
            ) from exc
        return native_recursive.packet_evaluate(
            bits, cast(TensorRing, self.work_ring),
            native.left_positions, native.row_cauchy, native.contributions,
            self.terms.desired, self.terms.tile_slots, native.right_positions,
        )

    def _evaluate_python(self, bits: tuple[int, ...]) -> Any:
        ring = self.work_ring
        desired = self.terms.desired
        if not desired:
            result = ring.one
            for _, left_pos, right_terms in self.geometry.row_terms:
                local = ring.zero
                for pos, displacement in right_terms:
                    if bits[pos]:
                        local = ring.add(local, self.cauchy[displacement])
                constant = local if bits[left_pos] else ring.sub(ring.one, local)
                result = ring.mul(result, constant)
                if result == ring.zero:
                    break
        else:
            coefficients: dict[tuple[int, ...], Any] = {
                (0,) * len(self.terms.target): ring.one,
            }
            for row, left_pos, right_terms in self.geometry.row_terms:
                local = ring.zero
                for pos, displacement in right_terms:
                    if bits[pos]:
                        local = ring.add(local, self.cauchy[displacement])
                ybit = bits[left_pos]
                constant = local if ybit else ring.sub(ring.one, local)
                contributions = tuple(
                    (index, coefficient if ybit else ring.neg(coefficient))
                    for index, coefficient in self.terms.contributions[row]
                )
                nxt: defaultdict[tuple[int, ...], Any] = defaultdict(lambda: ring.zero)
                for powers, value in coefficients.items():
                    nxt[powers] = ring.add(nxt[powers], ring.mul(value, constant))
                    for index, coefficient in contributions:
                        if powers[index] < desired[index]:
                            new_powers = list(powers)
                            new_powers[index] += 1
                            exponent = tuple(new_powers)
                            nxt[exponent] = ring.add(
                                nxt[exponent], ring.mul(value, coefficient),
                            )
                coefficients = nxt
            result = coefficients.get(desired, ring.zero)
        for mode, multiplicity, tile in self.terms.tile_bits:
            value = ring.zero
            for pos, coefficient in tile:
                if bits[pos]:
                    value = ring.add(value, ring.scalar(coefficient ** mode.b))
            result = ring.mul(result, ring.pow(value, multiplicity))
        return result
