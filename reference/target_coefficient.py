"""Experimental exact coefficient extraction without global exponent expansion.

A packet's target coefficient is the coefficient of x**beta in a product
of sparse affine linear forms. Two exact reductions are useful:

* Split the bipartite row-to-target-mode incidence graph into connected
  components. Their coefficients multiply, so exponent keys from unrelated
  components never need to be combined.
* Keep a partial exponent only when the still-unprocessed rows can supply
  every missing target exponent. This is a necessary condition, not a
  claim that the surviving states can all reach the target.

This reference algorithm is deliberately NOT production dispatch. Dense,
connected incidence can encode a permanent and still requires exponentially
many states; it does not prove a polynomial or non-exponential Sudoku solver.
"""
from __future__ import annotations

from dataclasses import dataclass
from collections.abc import Sequence

from non_exponential_sudoku.core.algebra import Padic
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.lazy_coefficients import NestedCoords


FiniteRing = Padic | JetRing


@dataclass(frozen=True, slots=True)
class LinearRow:
    constant: NestedCoords
    terms: tuple[tuple[int, NestedCoords], ...]


@dataclass(slots=True)
class ExtractionStats:
    components: int = 0
    largest_component_modes: int = 0
    peak_states: int = 0
    states_visited: int = 0
    retained_transitions: int = 0
    pruned_transitions: int = 0


def _check_rows(rows: Sequence[LinearRow], target: tuple[int, ...]) -> None:
    if not isinstance(target, tuple) or any(type(b) is not int or b < 0 for b in target):
        raise ValueError("target exponents must be nonnegative integers")
    for row in rows:
        if not isinstance(row, LinearRow):
            raise TypeError("expected explicit affine linear rows")
        for i, _ in row.terms:
            if type(i) is not int or not 0 <= i < len(target):
                raise ValueError("linear term references an invalid target mode")


def expanded_coefficient_reference(
    ring: FiniteRing, rows: Sequence[LinearRow], target: tuple[int, ...],
    *, stats: ExtractionStats | None = None,
) -> NestedCoords:
    """The original forward exponent-dictionary algorithm, as an oracle.

    Enumerates every attainable exponent vector <=target, even when it
    cannot possibly reach the requested coefficient using remaining rows.
    This is for bounded differential tests, never large-size dispatch.
    """
    _check_rows(rows, target)
    zero = (0,) * len(target)
    states: dict[tuple[int, ...], NestedCoords] = {zero: ring.one}
    if stats is not None:
        stats.peak_states = max(stats.peak_states, len(states))
    for row in rows:
        nxt: dict[tuple[int, ...], NestedCoords] = {}
        for powers, coefficient in states.items():
            if stats is not None:
                stats.states_visited += 1
                stats.retained_transitions += 1
            nxt[powers] = ring.add(
                nxt.get(powers, ring.zero), ring.mul(coefficient, row.constant),
            )
            for i, factor in row.terms:
                if powers[i] >= target[i]:
                    continue
                next_powers = powers[:i] + (powers[i] + 1,) + powers[i+1:]
                if stats is not None:
                    stats.retained_transitions += 1
                nxt[next_powers] = ring.add(
                    nxt.get(next_powers, ring.zero), ring.mul(coefficient, factor),
                )
        states = nxt
        if stats is not None:
            stats.peak_states = max(stats.peak_states, len(states))
    return states.get(target, ring.zero)


def _target_component(
    ring: FiniteRing,
    rows: Sequence[LinearRow],
    desired: tuple[int, ...],
    stats: ExtractionStats,
) -> NestedCoords:
    """One connected component, with future-row feasibility pruning."""
    count = len(desired)
    capacity = [0] * count
    for row in rows:
        for i in {i for i, _ in row.terms}:
            capacity[i] += 1
    if any(capacity[i] < desired[i] for i in range(count)):
        return ring.zero
    target_total = sum(desired)
    if target_total > len(rows):
        return ring.zero

    def viable(powers: tuple[int, ...], rows_left: int) -> bool:
        if target_total - sum(powers) > rows_left:
            return False
        return all(desired[i] - powers[i] <= capacity[i] for i in range(count))

    empty = (0,) * count
    states: dict[tuple[int, ...], NestedCoords] = {empty: ring.one}
    stats.peak_states = max(stats.peak_states, len(states))
    for row_index, row in enumerate(rows):
        # The current row is no longer available *after* this transition.
        for i in {i for i, _ in row.terms}:
            capacity[i] -= 1
        left = len(rows) - row_index - 1
        nxt: dict[tuple[int, ...], NestedCoords] = {}
        for powers, coefficient in states.items():
            stats.states_visited += 1
            if viable(powers, left):
                stats.retained_transitions += 1
                nxt[powers] = ring.add(
                    nxt.get(powers, ring.zero), ring.mul(coefficient, row.constant),
                )
            else:
                stats.pruned_transitions += 1
            for i, factor in row.terms:
                if powers[i] >= desired[i]:
                    continue
                raised = powers[:i] + (powers[i] + 1,) + powers[i+1:]
                if viable(raised, left):
                    stats.retained_transitions += 1
                    nxt[raised] = ring.add(
                        nxt.get(raised, ring.zero), ring.mul(coefficient, factor),
                    )
                else:
                    stats.pruned_transitions += 1
        states = nxt
        stats.peak_states = max(stats.peak_states, len(states))
        if not states:
            return ring.zero
    return states.get(desired, ring.zero)


def target_coefficient_by_components(
    ring: FiniteRing, rows: Sequence[LinearRow], target: tuple[int, ...],
    *, stats: ExtractionStats | None = None,
) -> NestedCoords:
    """Exact coefficient, decomposed by row/mode incidence and suffix demand.

    Deleting terms for a target exponent of zero is exact. A row with no
    remaining variable terms is a scalar factor. The resulting polynomial
    has independent components, so the coefficient of the target monomial
    is the product of component coefficients, in their source-row order.

    Retains only one component's coefficient dictionary at a time.
    """
    _check_rows(rows, target)
    observed = stats if stats is not None else ExtractionStats()
    positive = [i for i, b in enumerate(target) if b]
    if not positive:
        result = ring.one
        for row in rows:
            result = ring.mul(result, row.constant)
        return result

    parent = list(range(len(target)))

    def find(i: int) -> int:
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    def union(i: int, j: int) -> None:
        a, b = find(i), find(j)
        if a != b:
            parent[b] = a

    filtered_rows: list[LinearRow] = []
    available: set[int] = set()
    for row in rows:
        terms = tuple((i, value) for i, value in row.terms if target[i] > 0)
        filtered_rows.append(LinearRow(row.constant, terms))
        if terms:
            first = terms[0][0]
            available.update(i for i, _ in terms)
            for i, _ in terms[1:]:
                union(first, i)
    if any(i not in available for i in positive):
        return ring.zero

    groups: dict[int, list[int]] = {}
    for i in positive:
        groups.setdefault(find(i), []).append(i)
    component_rows: dict[int, list[LinearRow]] = {root: [] for root in groups}
    result = ring.one
    for row in filtered_rows:
        if not row.terms:
            result = ring.mul(result, row.constant)
        else:
            component_rows[find(row.terms[0][0])].append(row)
    observed.components = len(groups)
    observed.largest_component_modes = max(len(mode_ids) for mode_ids in groups.values())
    for root, component_modes in groups.items():
        local_index = {i: j for j, i in enumerate(component_modes)}
        local_rows = [
            LinearRow(row.constant, tuple((local_index[i], v) for i, v in row.terms))
            for row in component_rows[root]
        ]
        local_target = tuple(target[i] for i in component_modes)
        value = _target_component(ring, local_rows, local_target, observed)
        result = ring.mul(result, value)
        if result == ring.zero:
            break
    return result


def evaluate_packet_target_coefficient(
    entry: object, bits: tuple[int, ...],
    *, stats: ExtractionStats | None = None,
) -> NestedCoords:
    """Experimental full PacketEntry evaluation via target extraction.

    Reconstructs the exact local affine factors from the real prepared
    PacketEntry, then applies the unchanged source-tile factors. Refuses
    native and lazy rings: their equivalence/performance must be proved
    separately before production dispatch could use this algorithm.
    """
    from non_exponential_sudoku.contraction.packets import PacketEntry

    if not isinstance(entry, PacketEntry):
        raise TypeError("a prepared PacketEntry is required")
    ring = entry.work_ring
    if not isinstance(ring, (Padic, JetRing)) or getattr(entry, "native", None) is not None:
        raise TypeError("only eager Python packet entries are supported")
    rows: list[LinearRow] = []
    for row, left_pos, right_terms in entry.geometry.row_terms:
        local = ring.zero
        for pos, displacement in right_terms:
            if bits[pos]:
                local = ring.add(local, entry.cauchy[displacement])
        ybit = bits[left_pos]
        constant = local if ybit else ring.sub(ring.one, local)
        terms = tuple(
            (i, coefficient if ybit else ring.neg(coefficient))
            for i, coefficient in entry.terms.contributions[row]
        )
        rows.append(LinearRow(constant, terms))
    result = target_coefficient_by_components(ring, rows, entry.terms.desired, stats=stats)
    for mode, multiplicity, tile in entry.terms.tile_bits:
        value = ring.zero
        for pos, coefficient in tile:
            if bits[pos]:
                value = ring.add(value, ring.scalar(coefficient ** mode.b))
        result = ring.mul(result, ring.pow(value, multiplicity))
    return result
