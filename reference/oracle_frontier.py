"""Fail-closed structural work certificates for inherited packet-entry oracles.

A child network retains parent Vertex.oracle objects, not closures that
recursively invoke the parent network. This models one leaf assignment's
ORACLE frontier. Cost units are outer finite-ring calls, canonical scalar
coordinate copies, and non-ring integer/tuple allocations. They are not
bit-operation counts; the untrusted base-oracle work is kept explicit.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import prod
from collections.abc import Mapping

from non_exponential_sudoku.core.algebra import Padic
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.network import Network
from non_exponential_sudoku.contraction.packets import PacketEntry
from reference.packet_oracle_work import packet_evaluation_envelope


class UncertifiedOracle(ValueError):
    """No valid cost proof is attached to an ordinary input oracle."""


@dataclass(frozen=True)
class RingShape:
    extension_degree: int
    modulus: int
    precision: int
    # Inner Taylor variables first, outer variables last.
    jet_lengths: tuple[int, ...]

    @property
    def scalar_coordinates(self) -> int:
        return self.extension_degree * prod(self.jet_lengths)


def ring_shape(ring: Padic | JetRing) -> RingShape:
    lengths = []
    current: Padic | JetRing = ring
    while isinstance(current, JetRing):
        lengths.append(current.q)
        current = current.base  # type: ignore[assignment]
    if not isinstance(current, Padic):
        raise TypeError('finite Padic/JetRing required')
    return RingShape(current.e, current.f, current.p, tuple(reversed(lengths)))


@dataclass(frozen=True)
class LiftWorkEnvelope:
    """Shape-level steps for embed_element, NOT a full bit-cost theorem."""
    scalar_coordinate_masks: int
    source_integer_bit_ceiling: int
    source_tuple_nodes: int
    extra_jet_tuple_nodes: int
    extra_zero_tail_references: int

    @property
    def tuple_nodes(self) -> int:
        return self.source_tuple_nodes + self.extra_jet_tuple_nodes


def lift_work_envelope(source: Padic | JetRing, target: Padic | JetRing) -> LiftWorkEnvelope:
    """Shape cost of the exact canonical lift used by PacketEntry.__call__.

    Each pre-existing Taylor coordinate is visited once. Each Padic leaf
    masks e coefficients and constructs one tuple. Newly requested outer
    Taylor layers add a constant embedding and q-1 references to shared
    zero coefficients. Source value must already be canonical and must
    actually match the declared ring shape; this counts no validation.
    """
    src = ring_shape(source)
    dst = ring_shape(target)
    if (src.extension_degree != dst.extension_degree or src.modulus != dst.modulus
            or src.jet_lengths != dst.jet_lengths[:len(src.jet_lengths)]):
        raise ValueError('incompatible ring lift: extension or Taylor dimensions')
    if dst.precision < src.precision:
        raise ValueError('proof requires nondecreasing coefficient precision')
    sizes = src.jet_lengths
    nodes = sum(prod(sizes[i:]) for i in range(len(sizes) + 1))
    extra = dst.jet_lengths[len(sizes):]
    return LiftWorkEnvelope(
        scalar_coordinate_masks=src.scalar_coordinates,
        source_integer_bit_ceiling=max(src.precision, dst.precision),
        source_tuple_nodes=nodes,
        extra_jet_tuple_nodes=len(extra),
        extra_zero_tail_references=sum(q - 1 for q in extra),
    )


@dataclass(frozen=True)
class OracleFrontier:
    total_vertices: int
    packet_vertices: int
    input_vertices: int
    packet_ring_call_ceiling: int
    input_oracle_cost_sum: int
    canonical_lift_coordinate_ceiling: int
    tuple_nodes_ceiling: int
    zero_tail_reference_ceiling: int


def certify_oracle_frontier(
    net: Network, caller_ring: Padic | JetRing, *,
    input_oracle_costs: Mapping[int, int] | None = None,
) -> OracleFrontier:
    """One evaluation of every vertex oracle, excluding parent graph walks.

    The supplied costs for opaque oracles are independent *assumptions* in
    abstract operation units: do not interpret them as verified bit bounds.
    Each inherited PacketEntry is charged by its own creation ring, not by
    the ring of its current parent vertex. This counts distinct vertex calls,
    including multiple references to one oracle object.
    """
    input_costs = input_oracle_costs or {}
    p_count = i_count = ring_calls = input_sum = copies = nodes = tails = 0
    for vertex in net.left + net.right:
        oracle = vertex.oracle
        if isinstance(oracle, PacketEntry):
            local = packet_evaluation_envelope(oracle)
            lift = lift_work_envelope(oracle.R, caller_ring) if caller_ring is not oracle.R else None
            p_count += 1
            ring_calls += local.ring_calls
            if lift is not None:
                copies += lift.scalar_coordinate_masks
                nodes += lift.tuple_nodes
                tails += lift.extra_zero_tail_references
        else:
            key = id(oracle)
            if key not in input_costs:
                raise UncertifiedOracle(f'input oracle {vertex.name!r} has no cost premise')
            value = input_costs[key]
            if type(value) is not int or value < 0:
                raise UncertifiedOracle('input oracle cost must be a nonnegative integer')
            i_count += 1
            input_sum += value
    return OracleFrontier(
        total_vertices=len(net.left) + len(net.right),
        packet_vertices=p_count, input_vertices=i_count,
        packet_ring_call_ceiling=ring_calls, input_oracle_cost_sum=input_sum,
        canonical_lift_coordinate_ceiling=copies,
        tuple_nodes_ceiling=nodes, zero_tail_reference_ceiling=tails,
    )


def inherited_oracle_identity(parent: Network, child: Network) -> bool:
    """Check actual make_child/CompiledChildPlan topology preservation.

    New right-side oracles must be packet entries. Every retained left-side
    oracle must be an identical object from the parent's vertices. This
    explicitly checks pointers, not names (which may be duplicated).
    """
    old_ids = {id(v.oracle) for v in parent.left + parent.right}
    return (all(id(v.oracle) in old_ids for v in child.left)
            and all(isinstance(v.oracle, PacketEntry) for v in child.right))
