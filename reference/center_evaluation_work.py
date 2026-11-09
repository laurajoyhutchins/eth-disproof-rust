"""Paper-center factor work: symbolic outer-operation and child-call bounds.

These envelopes are conditional on the actual paper packing premises, one
canonical Padic center, a positive-weight mode catalog, and the Python mode
eliminator. They bound *how many* local table/child operations can occur, not
child bit costs, coefficient preparation, native kernels or solver totality.

No 2**support exponent is ever materialized for symbolic paper sizes.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import isqrt


def _ceil_log2(n: int) -> int:
    if n < 1:
        raise ValueError("ceil(log2(n)) needs positive integer")
    return (n - 1).bit_length()


def _ceil_sqrt(n: int) -> int:
    q = isqrt(n)
    return q + int(q * q < n)


@dataclass(frozen=True)
class CenterWorkEnvelope:
    """Conservative per-center log2 operation ceilings, not time bounds.

    A <= 2**support_exponent. Child calls <= F*A per deformation.
    Python elimination ring calls <= 64*(k+1)*(F+1)*(p+1)**3*(A+1)**2.
    For one center, multiply these by the Newton sample count.
    """

    edges: int
    vertices: int
    packets: int
    slots: int
    center_valuation: int
    center_precision: int
    sample_count: int
    colors_per_weight: int
    mode_count_ceiling: int
    factor_count_ceiling: int
    support_exponent: int
    log2_factor_child_calls: int
    log2_center_child_calls: int
    log2_factor_join_pairs: int
    log2_center_ring_calls: int
    interpolation_ring_calls: int

    def child_call_capacity_small(self, *, exponent_limit: int = 30) -> int:
        """Materialize an illustrative *ceiling* only when safely small."""
        if self.support_exponent > exponent_limit:
            raise ValueError("symbolic capacity is intentionally not materialized")
        return self.sample_count * self.factor_count_ceiling * (1 << self.support_exponent)


def paper_center_work_envelope(
    *, edges: int, vertices: int, packet_count: int, slots: int,
    groups: int, active_coordinates: int, center_valuation: int,
    base_precision: int,
) -> CenterWorkEnvelope:
    """Bound local factor-table work for one evaluated paper center.

    Preconditions: a>=2u, i<u, P*L<=3M, r=groups, M>=u,
    p>=1, r=64, and paper/interpolate with Python factor elimination.
    Mode colors per weight K=P*2**(i+1); their global positive-weight
    domain has at most 2**(4 ceil(sqrt(K*pt))) assignments.

    Child contractions are excluded from local ring-call counts; their total
    is separately bounded. Formula uses deliberately coarse constants and
    counts both Python sparse and Python enumerate join algorithms.
    """
    fields = (edges, vertices, packet_count, slots, groups,
              active_coordinates, center_valuation, base_precision)
    if any(type(x) is not int for x in fields):
        raise ValueError("integer parameters required")
    if (edges < active_coordinates or vertices < 0 or packet_count < 0
            or base_precision < 1 or groups != 64 or active_coordinates < 1
            or slots < 4 or (slots & (slots - 1))
            or not 0 <= center_valuation < active_coordinates
            or 2 * active_coordinates > slots.bit_length() - 1
            or packet_count * slots > 3 * edges):
        raise ValueError("paper-active packing and center assumptions required")
    a = slots.bit_length() - 1
    h = (3 * edges + active_coordinates - 1) // active_coordinates
    pt = (base_precision + 8 * h * (slots >> center_valuation)
          + 8 * edges * (a + 1))
    samples = edges * (2 * slots - 1) + 1
    K = packet_count * (1 << (center_valuation + 1))
    k = K * (pt - 1)
    # Each group-component factor is associated with a connected component
    # containing a retained vertex or a nonempty packet. An unsplit group can
    # produce one factor even if its incidence is empty.
    F = groups * (vertices + packet_count + 1)
    alpha = 4 * _ceil_sqrt(K * pt)
    log_child = alpha + _ceil_log2(F)
    log_center_child = log_child + _ceil_log2(samples)
    # At most k eliminations, F-1 joins per elimination, and A**2 pairs per
    # join. If k=0 the expression is a conservative nonzero ceiling.
    log_pairs = 2 * alpha + _ceil_log2(max(1, k * F))
    # Coarse table-ring-op ceiling on one deformation: factor build, sparse
    # joins, enumerated projections, final multiplication, plus headroom for
    # repeated factor lookups. Each polynomial has at most pt coefficients.
    # Non-ring integer-key work and cache/child preparation are not included.
    prefactor = 64 * (k + 1) * (F + 1) * (pt + 1) ** 3
    log_ring = 2 * (alpha + 1) + _ceil_log2(prefactor) + _ceil_log2(samples)
    # Newton interpolation calls (add/sub/mul/inv) from bit_work.py. Each
    # counts a ring operation, not the cost of the implementation's inv.
    upper = (5 * samples * (samples + 1)) // 2 + samples
    interp_calls = 2 * upper + samples
    return CenterWorkEnvelope(
        edges, vertices, packet_count, slots, center_valuation, pt,
        samples, K, k, F, alpha, log_child, log_center_child,
        log_pairs, log_ring, interp_calls,
    )


def table_child_call_bound(*, factors: int, admissible_assignments: int) -> int:
    """Finite structural ceiling; small-case oracle for instrumentation.

    A factor builder evaluates each admissible local assignment once. No
    table-building short-circuit can increase this count. This routine does
    not assume independent factors or nonzero coefficient values.
    """
    if any(type(v) is not int or v < 0 for v in (factors, admissible_assignments)):
        raise ValueError("nonnegative integer counts required")
    return factors * admissible_assignments


def ring_convolution_upper(*, eliminations: int, factors: int,
                           factor_rows: int, precision: int) -> int:
    """Loose outer ring-operation ceiling for the factor algorithm.

    A factor polynomial contains <=p nonzero degrees; any join processes at
    most A*A row pairs, and each convolution <=p*p coefficient pairs.
    The enumerate path scans <=A projected rows and <=p multiplicities.
    The bound includes initialization and final polynomial multiplication.
    It excludes the calls made while evaluating each child and all Python
    integer/hash/ordering work.
    """
    vals = (eliminations, factors, factor_rows, precision)
    if any(type(v) is not int or v < 0 for v in vals) or precision < 1:
        raise ValueError("nonnegative counts and positive precision required")
    return (64 * (eliminations + 1) * (factors + 1) *
            (factor_rows + 1) ** 2 * (precision + 1) ** 3)
