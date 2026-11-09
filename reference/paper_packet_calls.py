"""Conditional outer-ring-call envelope for all paper-mode packet entries.

This is a *symbolic call-count lemma*, not a bit-operation bound. It
combines actual PacketEntry._evaluate_python loops, the existing paper
mode-catalog count and reachable-state proof, and conditional child
shrinkage/fanout. Crucially it never constructs the exponent dictionary.
"""
from __future__ import annotations

from dataclasses import dataclass

from reference.paper_mode_reachability import (
    paper_mode_count_ceiling, uniform_paper_packet_bound,
)


def ceil_log2_positive(n: int) -> int:
    if type(n) is not int or n < 1:
        raise ValueError("positive integer required")
    return (n - 1).bit_length()


@dataclass(frozen=True, slots=True)
class PaperPacketCallEnvelope:
    """Conditional paper-accepted source-Python packet ring call counts.

    The count assumes that every local mode is from the paper mode catalog,
    all packet rows/slots originate from valid incidence, and the child
    shrinkage and potential-fanout premises hold. It excludes original
    callbacks, coefficient preparation, native/lazy paths, integer-power
    construction, canonical lift bit work, and resource-limit refusals.
    """

    input_scale: int
    max_slots: int
    max_precision: int
    max_modes_per_packet: int
    log2_reachable_coefficient_states: int
    log2_ring_calls_per_packet_entry: int
    log2_packet_descriptors_per_path: int
    log2_packet_calls_per_potential_leaf: int
    log2_outer_ring_calls_per_potential_leaf: int
    log2_potential_nodes: int
    log2_total_outer_ring_calls: int
    universal_bit_bound_proven: bool = False


def paper_packet_entry_ring_calls_log2(*, slots: int, precision: int) -> int:
    """Ceil log2 a *conservative* source-loop bound for one packet call.

    Every valid paper packet has <=L rows, <=L right terms per row,
    and <=K=L*(p-1) active modes of either source or target type.
    For target modes, exponent vectors after j rows have sum<=j, hence
    at most (K+1)**L states per row (the existing reachable-state
    lemma). Each row runs at most (1+K) transitions per state,
    plus <=L local additions, <=K negations and one subtraction.
    Each of <=K source tiles has <=L slot contributions, then one
    ring pow and mul.

    Consequently 64*(L+1)**2*(K+1)*(K+1)**L is an upper bound
    for the *outer* calls to add/sub/neg/mul/scalar/pow, including
    both the zero-target and nonzero-target branches. The returned
    exponent rounds this upward to a power of two without constructing
    either (K+1)**L or a packet oracle.

    The Python integer expression j**mode.b and the bit costs of
    ring operations are separate: this cannot be a bit-time certificate.
    """
    if (type(slots) is not int or slots < 2 or slots & (slots - 1)
            or type(precision) is not int or precision < 1):
        raise ValueError("power-of-two packet slots>=2 and positive precision required")
    modes = paper_mode_count_ceiling(precision, slots)
    return (6 + 2 * ceil_log2_positive(slots + 1)
            + (slots + 1) * ceil_log2_positive(modes + 1))


def uniform_paper_packet_calls(
    *, s: int, initial_edges: int, initial_vertices: int,
    initial_precision: int, max_terminal_edges: int,
    potential_nodes_log2: int,
) -> PaperPacketCallEnvelope | None:
    """Lift the conditional local packet lemma to the whole POTENTIAL tree.

    Every packet descriptor is created on some shrinking root-to-leaf
    chain. The lineage theorem gives <=V0+floor(32*M0/29) visible
    vertices, and each packet entry is evaluated at most 2**M times
    in one direct call, plus <=2**M factor-table rows if uncompiled
    elimination later falls back to direct. Zero-support on packets
    is *structural* and invokes no packet arithmetic.

    Potential nodes include zero-certified candidate children, not
    just executed ContractionEngine frames. No bound on actual
    process memory, primitive bit work, or resource non-refusal follows.
    """
    values = (s, initial_edges, initial_vertices, initial_precision,
              max_terminal_edges, potential_nodes_log2)
    if any(type(x) is not int for x in values):
        raise ValueError("all inputs must be exact integers")
    if (s < 2 or not 0 <= initial_edges <= s
            or not 0 <= initial_vertices <= s * s
            or not 1 <= initial_precision <= s
            or not 0 <= max_terminal_edges <= s
            or potential_nodes_log2 < 0):
        raise ValueError("invalid paper input shape, terminal or fanout")
    paper = uniform_paper_packet_bound(
        s=s, initial_edges=initial_edges,
        initial_precision=initial_precision,
    )
    if paper.maximum_slots == 0:
        return None  # paper schedule never activates a new packet
    max_descriptors = initial_vertices + 32 * initial_edges // 29
    if max_descriptors == 0:
        raise ValueError("active paper frame requires an existing vertex")
    per_entry = paper_packet_entry_ring_calls_log2(
        slots=paper.maximum_slots, precision=paper.maximum_precision,
    )
    descriptor_log = ceil_log2_positive(max_descriptors)
    # direct full assignment + possible prior factor table: <=2^(M+1)
    per_leaf_calls = descriptor_log + max_terminal_edges + 1
    per_leaf_ring = per_leaf_calls + per_entry
    return PaperPacketCallEnvelope(
        input_scale=s,
        max_slots=paper.maximum_slots,
        max_precision=paper.maximum_precision,
        max_modes_per_packet=paper.maximum_target_modes,
        log2_reachable_coefficient_states=paper.log2_local_state_ceiling,
        log2_ring_calls_per_packet_entry=per_entry,
        log2_packet_descriptors_per_path=descriptor_log,
        log2_packet_calls_per_potential_leaf=per_leaf_calls,
        log2_outer_ring_calls_per_potential_leaf=per_leaf_ring,
        log2_potential_nodes=potential_nodes_log2,
        log2_total_outer_ring_calls=potential_nodes_log2 + per_leaf_ring,
    )
