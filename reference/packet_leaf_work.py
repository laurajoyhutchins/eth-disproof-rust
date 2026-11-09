"""Bound implicit packet-oracle *calls* in one actual Python leaf attempt.

The earlier packet_evaluation_envelope proves outer ring-call counts for ONE
already-prepared eager Python PacketEntry. This module multiplies those
counts by every place the actual leaf evaluator can invoke packet entries.

The bound is deliberately local to a concrete instantiated Network. It
cannot certify all possible packet descriptors, generated mode assignments,
Cauchy preparation, native kernels, or the paper recurrence's global fanout.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from non_exponential_sudoku.contraction.packets import PacketEntry
from non_exponential_sudoku.core.algebra import Padic
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.network import Network
from reference.oracle_frontier import lift_work_envelope
from reference.packet_oracle_work import packet_evaluation_envelope


class UncertifiedPacketLeaf(ValueError):
    """No source-consistent envelope exists for the requested packet path."""


def _ceil_log2(n: int) -> int:
    if n < 1:
        raise ValueError("positive integer expected")
    return (n - 1).bit_length()


def _log2_sum(terms: list[int]) -> int:
    """Ceil log2 of an upper bound on sum(2**terms), without huge powers."""
    if not terms:
        return 0
    return max(terms) + _ceil_log2(len(terms))


@dataclass(frozen=True, slots=True)
class PacketLeafWork:
    """Base-two ceilings, *not* exact totals or bit-operation complexity.

    * A direct leaf can invoke every packet entry once per Boolean assignment.
    * A compiled leaf evaluates each entry once per input factor-table row.
    * The uncompiled path can build tables and then fall back to direct.
    * Zero-support checks inspect packet structure, NOT PacketEntry.__call__.
    * The recorded lift visits are masks of existing canonical coordinates,
      not a source-and-target ring bit-operation theorem.
    """

    edges: int
    packet_vertices: int
    max_packet_arity: int
    leaf_strategy: Literal["enumerate", "eliminate"]
    zero_support: bool
    direct_packet_calls_log2: int
    dense_table_packet_calls_log2: int
    structural_support_rows_log2: int
    per_attempt_packet_calls_log2: int
    per_attempt_outer_ring_calls_log2: int
    per_attempt_lift_coordinate_masks_log2: int
    potential_attempts_log2: int | None
    total_outer_ring_calls_log2: int | None
    total_lift_coordinate_masks_log2: int | None
    source_correspondence_only: bool = True
    universal_bit_bound_proven: bool = False


def certify_packet_leaf_work(
    net: Network, caller_ring: Padic | JetRing, *,
    leaf_strategy: Literal["enumerate", "eliminate"] = "eliminate",
    zero_support: bool = False,
    potential_attempts_log2: int | None = None,
) -> PacketLeafWork:
    """Charge every instantiated packet oracle, including fallback and lift.

    The per-entry evaluator is certified only if it uses the eager Python
    Padic/JetRing path. A memo hit or support short-circuit may reduce work.
    No native, lazy-expression or arbitrary callback path receives a bound.

    The optional potential attempt count is an independent assumption. Its
    meaning must include zero-certified attempts, even when they never
    enter a recursive contract frame; it is not established by this function.
    """
    if not isinstance(net, Network) or not isinstance(caller_ring, (Padic, JetRing)):
        raise UncertifiedPacketLeaf("finite Network and eager caller ring required")
    if leaf_strategy not in ("enumerate", "eliminate") or type(zero_support) is not bool:
        raise ValueError("unsupported leaf strategy or zero-support policy")
    if (potential_attempts_log2 is not None and
            (type(potential_attempts_log2) is not int or potential_attempts_log2 < 0)):
        raise ValueError("potential attempt count requires a nonnegative log2 bound")
    net.validate()
    direct_count_terms: list[int] = []
    table_count_terms: list[int] = []
    direct_ring_terms: list[int] = []
    table_ring_terms: list[int] = []
    direct_lift_terms: list[int] = []
    table_lift_terms: list[int] = []
    max_arity = 0
    count = 0
    for vertex in net.left + net.right:
        entry = vertex.oracle
        if not isinstance(entry, PacketEntry):
            continue
        # The actual child constructor's port map assigns each local bit
        # position exactly once. Reject manually forged/desynchronized views.
        ports = entry.geometry.port_map
        if (sorted(ports.values()) != list(range(len(vertex.ports))) or
                len(vertex.ports) > net.edges):
            raise UncertifiedPacketLeaf("packet geometry does not match vertex ports")
        for _, bit, rights in entry.geometry.row_terms:
            if not 0 <= bit < len(vertex.ports) or any(
                not 0 <= pos < len(vertex.ports) for pos, _ in rights
            ):
                raise UncertifiedPacketLeaf("packet geometry has invalid bit positions")
        for _, _, tile in entry.terms.tile_bits:
            if any(not 0 <= bit < len(vertex.ports) for bit, _ in tile):
                raise UncertifiedPacketLeaf("packet source tile has invalid bit positions")
        try:
            local = packet_evaluation_envelope(entry)
            lift = (lift_work_envelope(entry.R, caller_ring)
                    if caller_ring is not entry.R else None)
        except (TypeError, ValueError, AttributeError) as exc:
            raise UncertifiedPacketLeaf("packet uses uncertified native/lazy/precision path") from exc
        count += 1
        arity = len(vertex.ports)
        max_arity = max(max_arity, arity)
        direct_count_terms.append(net.edges)
        table_count_terms.append(arity)
        if local.ring_calls:
            size_log = _ceil_log2(local.ring_calls)
            direct_ring_terms.append(net.edges + size_log)
            table_ring_terms.append(arity + size_log)
        if lift is not None and lift.scalar_coordinate_masks:
            size_log = _ceil_log2(lift.scalar_coordinate_masks)
            direct_lift_terms.append(net.edges + size_log)
            table_lift_terms.append(arity + size_log)
    if count == 0:
        raise UncertifiedPacketLeaf("no generated packet entries to certify")
    # Any eventual zero-support probe runs *before* the leaf. It scans
    # packet structure without evaluating PacketEntry's ring arithmetic.
    support_rows = _log2_sum(table_count_terms) if zero_support else 0
    entry_terms = list(direct_count_terms)
    ring_terms = list(direct_ring_terms)
    lift_terms = list(direct_lift_terms)
    if leaf_strategy == "eliminate":
        entry_terms += table_count_terms
        ring_terms += table_ring_terms
        lift_terms += table_lift_terms
    total_ring_log = _log2_sum(ring_terms)
    total_lift_log = _log2_sum(lift_terms)
    return PacketLeafWork(
        edges=net.edges, packet_vertices=count, max_packet_arity=max_arity,
        leaf_strategy=leaf_strategy, zero_support=zero_support,
        direct_packet_calls_log2=_log2_sum(direct_count_terms),
        dense_table_packet_calls_log2=_log2_sum(table_count_terms),
        structural_support_rows_log2=support_rows,
        per_attempt_packet_calls_log2=_log2_sum(entry_terms),
        per_attempt_outer_ring_calls_log2=total_ring_log,
        per_attempt_lift_coordinate_masks_log2=total_lift_log,
        potential_attempts_log2=potential_attempts_log2,
        total_outer_ring_calls_log2=(
            None if potential_attempts_log2 is None
            else potential_attempts_log2 + total_ring_log
        ),
        total_lift_coordinate_masks_log2=(
            None if potential_attempts_log2 is None
            else potential_attempts_log2 + total_lift_log
        ),
    )
