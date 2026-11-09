"""Conditional work envelope for PAPER child preparation and Cauchy contexts.

Correspondence: contraction/packets.py (eager Padic context and cross terms),
contraction/children.py, contraction/compiled_children.py.  These are counts
of outer ring calls and structural index visits, NOT CPython instructions.

The input network and mode descriptors must be finite, well-formed and have
bounded explicit names; original vertex-oracle callbacks are *referenced*,
not evaluated or proved inexpensive here. Native/lazy contexts are excluded.
"""
from __future__ import annotations

from dataclasses import dataclass

from reference.nested_ring_bit_cost import finite_shape_bit_envelope


class UncertifiedPreparation(ValueError):
    """Refuse to substitute unbounded metadata or malformed paper premises."""


@dataclass(frozen=True, slots=True)
class RingCalls:
    scalar: int = 0
    add: int = 0
    mul: int = 0
    inv: int = 0
    pow: int = 0

    def __add__(self, other: RingCalls) -> RingCalls:
        return RingCalls(self.scalar + other.scalar, self.add + other.add,
                         self.mul + other.mul, self.inv + other.inv,
                         self.pow + other.pow)

    def scale(self, factor: int) -> RingCalls:
        if type(factor) is not int or factor < 0:
            raise ValueError('nonnegative multiplier required')
        return RingCalls(self.scalar * factor, self.add * factor,
                         self.mul * factor, self.inv * factor,
                         self.pow * factor)


def cauchy_context_calls(slots: int) -> RingCalls:
    """Exact ring calls in EvaluationContext's normal cauchy_values path.

    Valid for nonzero t in (-L,L), eager Padic, without lazy checkpoints.
    L=2 has a separate direct product fast path. The resulting cauchy[t]
    is reused as the shared numerator; no second factorization occurs.
    """
    if type(slots) is not int or slots < 2 or slots & (slots - 1):
        raise ValueError('power-of-two packet slots >= 2 required')
    if slots == 2:
        return RingCalls(scalar=10, add=3, mul=18, inv=1)
    return RingCalls(scalar=6 * slots - 2, add=2 * slots - 1,
                     mul=14 * slots - 5, inv=1)


CROSS_MISS_CALLS = RingCalls(scalar=4, add=1, mul=6, inv=1, pow=1)


@dataclass(frozen=True, slots=True)
class PreparedChildWork:
    """Constructive overestimate for *one* uncached child preparation.

    This does not include contracting the child or evaluating its oracles.
    It charges a fresh context separately because production shares the
    context across sibling child evaluations for one deformation sample.
    The generic modes count may overstate the actual packet-local subsets.
    """

    edges: int
    vertices: int
    packets: int
    slots: int
    modes: int
    extension_degree: int
    precision: int
    input_name_bits: int
    mode_count_limit: int
    catalog_index_visits: int
    port_visits: int
    membership_comparisons: int
    tile_tuple_entries: int
    cross_misses: int
    preparation_ring_calls: RingCalls
    center_ring_calls: RingCalls
    max_integer_operand_bits: int
    prepared_value_slots: int
    prepared_payload_bits: int
    abstract_index_visits: int
    schoolbook_bit_work_majorant: int


def prepared_child_work(*, edges: int, vertices: int, packets: int, slots: int,
                        modes: int, precision: int, extension_degree: int,
                        input_name_bits: int) -> PreparedChildWork:
    """Bound construction under actual paper packing and catalog hypotheses.

    Assumes P*L <= 3*M, M>=0, V>=0, one mode of each positive weight per
    packet/y0, and y0 range <= L (true at evaluated paper centers). The
    parent input's names are explicitly bounded by input_name_bits. Each
    generated child adds only a fixed prefix per retained vertex, so along
    <=log2(s) paper depths total name growth remains polynomial when names
    start polynomially bounded.

    Ring operations assume the eager *reference* Padic implementation with
    canonical inputs and a supplied irreducible polynomial. The schoolbook
    majorant excludes native kernels, arbitrary vertex callback internals,
    true process RSS, and creation of the initial irreducible polynomial.
    """
    values = (edges, vertices, packets, slots, modes, precision,
              extension_degree, input_name_bits)
    if any(type(x) is not int for x in values):
        raise UncertifiedPreparation('exact integers required')
    if (edges < 0 or vertices < 0 or packets < 0 or modes < 0
            or precision < 1 or extension_degree < 2 or input_name_bits < 0
            or slots < 2 or slots & (slots - 1)):
        raise UncertifiedPreparation('invalid finite network or coefficient shape')
    if packets * slots > 3 * edges:
        raise UncertifiedPreparation('packet-count lemma not established')
    max_catalog = packets * slots * (precision - 1)
    if modes > max_catalog:
        raise UncertifiedPreparation('mode-catalog bound violated')

    # The direct construction builds owner and slot maps once, then each
    # PacketEntry without a compiled geometry scans the source left owners
    # once more. Each packet has L slots; each target mode has <=L rows.
    # The cached compiled-plan path is no worse for these quantities.
    ports = 2 * edges + packets * (edges + 4 * slots) + 2 * vertices
    # The standalone catalog scans at most L columns for each of at most
    # L values of y0 per packet, and copies O(L) slots for <=P*L*(p-1)
    # modes. It is constructed once per center valuation unless cached.
    catalog_visits = (2 * edges + packets * (
        2 * slots + 2 * slots * slots +
        3 * slots * slots * (precision - 1)))
    memberships = packets * slots * modes * slots
    tiles = packets * modes * slots
    # There can be at most L selected rows and m active target modes per
    # PacketEntry, hence <=P*L*m distinct cross coefficient requests.
    cross = packets * slots * modes
    calls = CROSS_MISS_CALLS.scale(cross)
    context = cauchy_context_calls(slots)

    # Finite, explicit metadata: O(log(M+V+P+L+p)) bits per index; parent
    # vertex names are copied at most once per retained kept vertex, and
    # one fixed prefix is added per recursive level. Avoid treating a Python
    # callback's implementation/body as part of that metadata certificate.
    idx_bits = max(1, (edges + vertices + packets + slots + modes + precision + 1).bit_length())
    integer_operand = (2 * slots - 1) * max(1, slots.bit_length()) + precision + idx_bits
    # These are *slots of scalar ring values*, not an RSS bound or an assertion
    # that every slot has a privately owned coefficient allocation.
    coefficient_slots = 2 * slots + cross
    payload = coefficient_slots * extension_degree * precision
    scans = (ports + packets * slots * slots + memberships + tiles + cross +
             packets * (modes + slots + 1) + vertices + input_name_bits + 1)
    ring = finite_shape_bit_envelope(extension_degree, precision)
    # Odd denominator construction and per-mode index/scalar manipulation are
    # charged with a generous cubic schoolbook allowance per bounded visit.
    # This is a mathematical algorithm-cost majorant, not an instruction count.
    integer_work = 1024 * (scans + 4 * slots * slots + 1) * (integer_operand + 1) ** 3
    ring_work = (calls.add * ring.add_bits + calls.mul * ring.mul_bits
                 + calls.inv * ring.inv_bits
                 + calls.pow * ring.pow_bits(precision)
                 + calls.scalar * 128 * (integer_operand + ring.canonical_payload_bits + 1)**2)
    return PreparedChildWork(
        edges, vertices, packets, slots, modes, extension_degree, precision,
        input_name_bits, max_catalog, catalog_visits, ports, memberships, tiles, cross,
        calls, context, integer_operand, coefficient_slots, payload,
        scans, integer_work + ring_work,
    )
