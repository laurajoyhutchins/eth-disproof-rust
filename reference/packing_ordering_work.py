"""Source-loop bit-work envelopes for paper packing and mode elimination ordering.

These are conditional *abstract schoolbook* bit-operation majorants, not
measurements of CPython execution, proof of the packing lemma's conclusions,
or physical allocation guarantees. No coefficient oracle is evaluated here.
"""
from __future__ import annotations

from dataclasses import dataclass


def _positive_integer(value: int, name: str) -> None:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def _ceil_log2_positive(value: int) -> int:
    return (value - 1).bit_length()


@dataclass(frozen=True, slots=True)
class PackingSourceWork:
    edges: int
    vertices: int
    groups: int
    coordinates: int
    slots: int
    full_label_bits: int
    maximum_packet_count: int
    maximum_allocated_packet_slots: int
    score_pair_visits: int
    abstract_schoolbook_bit_work: int


def packing_source_work(*, edges: int, vertices: int, groups: int,
                        coordinates: int) -> PackingSourceWork:
    """Overbound actual balanced_labels, pack, and audit_packing source loops.

    There are <=M populated endpoint-label classes and <=M normalized
    symbol-pair families. Their global padded height Hpad satisfies
    Hpad < M+L (M>0). Each family generates <=Hpad packets, each
    visiting O(L*a) slot and symbol entries. A pair of vertices can be
    compared at most once in each side's label-scoring pass, with an
    O(M)-length sparse histogram scan. We allow quadratic collection
    operations for worst-case built-in dictionary/set key collisions.

    Integer arithmetic assumes schoolbook operations and bounded integer
    labels/indices. This deliberately overbounds source-level loops with a
    high-degree polynomial; it does not certify input-oracle callback work.
    """
    for name, value in (("edges", edges), ("vertices", vertices),
                        ("groups", groups), ("coordinates", coordinates)):
        _positive_integer(value, name)
    if groups < 1 or coordinates < 1:
        raise ValueError("positive groups and coordinates required")
    L = 1 << coordinates
    M, V = edges, vertices
    # r**a can be huge numerically, but its *representation width* is O(a log r).
    bits = (coordinates * _ceil_log2_positive(groups + 1)
            + 8 * _ceil_log2_positive(M + V + L + 2) + 8)
    max_packets = M * (M + L)
    max_slots = max_packets * L
    score_visits = V * (V - 1) // 2 * max(1, M)
    # Source loops are <= degree 5 in (M+V+L) before accounting for
    # at most quadratic hash-table collisions and schoolbook integer work.
    # The degree-8 envelope includes those two costs, sorting and the
    # orientation/materialization loops even if nothing is cached.
    span = M + V + L + 2
    work = (1024 * span**8 * (coordinates + 1)**3
            * (bits + 1)**3)
    return PackingSourceWork(
        M, V, groups, coordinates, L, bits, max_packets, max_slots,
        score_visits, work,
    )


@dataclass(frozen=True, slots=True)
class ModeOrderingWork:
    variables: int
    initial_factors: int
    precision: int
    selections: int
    maximum_live_factors: int
    maximum_score_bits: int
    maximum_scope_pair_inspections: int
    abstract_schoolbook_bit_work: int


def mode_ordering_work(*, variables: int, factors: int,
                       precision: int) -> ModeOrderingWork:
    """Bound all calls to select_variable, for both order strategies.

    Every elimination removes at least one incident factor and adds at
    most one, so the live factor count is <=F+m. Scope sizes are <=m.
    Each candidate builds products of <=m domain sizes, each <=p, with
    <=m*ceil(log2(p+1)) bits. Even the min_fill nested candidate pair
    scan, adjacency creation and exact Python big-integer comparisons are
    polynomial in F,m,log p. This bound deliberately allows quadratic
    collisions for constructed set/dictionary lookups.
    """
    for name, value in (("variables", variables), ("factors", factors),
                        ("precision", precision)):
        _positive_integer(value, name)
    if precision < 1:
        raise ValueError("precision must be positive")
    m, F = variables, factors
    max_live = F + m
    score_bits = (m * _ceil_log2_positive(precision + 1)
                  + 4 * _ceil_log2_positive(m + 2) + 8)
    # Allow m selections; each handles <=m candidate variables and
    # <=F+m factor scopes. Each scope has <=m entries. The m^4
    # allowance dominates adjacency and min-fill pair comparisons.
    inspections = m * (m + 1)**4 * (F + m + 1)
    work = 1024 * (inspections + 1) * (m + 1)**2 * (score_bits + 1)**3
    return ModeOrderingWork(
        m, F, precision, m, max_live, score_bits, inspections, work,
    )
