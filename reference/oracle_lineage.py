"""Reference oracle-lineage invariant for direct and compiled recursive children.

This is a source-correspondence audit, not a runtime optimization. Existing
vertex callables are *referenced*, never recursively wrapped or copied into a
new packet-entry evaluator. New packet entries contain prepared finite-ring
coefficients and modes; their call costs and any arbitrary inherited callback
costs require separate theorems.

The paper path bound assumes all generated children satisfy the source's
3*M/32 shrinkage check. It applies to ONE root-to-leaf path, not to the
whole recursion tree or the memory of cached sibling networks.
"""
from __future__ import annotations

from dataclasses import dataclass

from non_exponential_sudoku.contraction.children import ChildComponent
from non_exponential_sudoku.contraction.packets import PacketEntry
from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.core.packing import Packing


class OracleLineageError(ValueError):
    """The observed child violates the direct-reference constructor contract."""


@dataclass(frozen=True, slots=True)
class ChildOracleLineage:
    parent_vertices: int
    inherited_vertices: int
    inherited_packet_vertices: int
    new_packet_vertices: int
    packet_count: int
    child_vertices: int


@dataclass(frozen=True, slots=True)
class PaperPathOracleBound:
    root_edges: int
    root_vertices: int
    max_new_packet_descriptors: int
    max_vertices: int
    applies_only_to_successful_paper_shrinkage: bool = True
    root_input_name_bits: int | None = None
    max_visible_name_bits: int | None = None


def paper_single_path_descriptor_bound(
    *, root_edges: int, root_vertices: int,
    root_input_name_bits: int | None = None,
) -> PaperPathOracleBound:
    """Bound the number of distinct packet descriptors on one *paper* path.

    Each packet owns >=1 distinct original edge, so P_d<=M_d. On successful
    active child edges, 32*M_(d+1)<=3*M_d. Summing the geometric upper
    bound over *all* depths gives sum_d P_d<=floor(32*M_0/29).
    At depth d the child retains each parent vertex at most once and creates
    <=P_d new packet vertices; hence V_d<=V_0+sum_(j<d)P_j.

    If root_input_name_bits is supplied, the result additionally bounds the
    total *UTF-8 name bits* simultaneously visible along the path. The paper
    implementation uses 64 groups and writes only names of the form
    `packet:{k}:g{group}`. Each packet ID k<M0 needs at most
    max(1,M0.bit_length()) decimal digits, while group<64 needs at most
    6 digits. Thus each generated name uses at most
    8*(9+max(1,M0.bit_length())+6) bits.

    Counts only descriptors / vertex references and their names. Original
    oracle *bodies*, packet coefficient payloads, caches, sibling branches,
    intermediate arithmetic and total computation time are not bounded here.
    """
    if (type(root_edges) is not int or type(root_vertices) is not int
            or root_edges < 0 or root_vertices < 0):
        raise ValueError("nonnegative integer edge and vertex counts required")
    if (root_input_name_bits is not None and
            (type(root_input_name_bits) is not int or root_input_name_bits < 0)):
        raise ValueError("root input name bit length must be a nonnegative integer")
    created = 32 * root_edges // 29
    max_name_bits = None if root_input_name_bits is None else (
        root_input_name_bits +
        created * 8 * (9 + max(1, root_edges.bit_length()) + 6)
    )
    return PaperPathOracleBound(
        root_edges, root_vertices, created, root_vertices + created,
        root_input_name_bits=root_input_name_bits,
        max_visible_name_bits=max_name_bits,
    )


def _verify_parent_packing(net: Network, packing: Packing) -> None:
    """Recheck only the actual source-incidence packet ownership property."""
    if packing.a < 1:
        raise OracleLineageError("a positive packet exponent is required")
    width = 1 << packing.a
    owned: list[int] = []
    for packet in packing.packets:
        if len(packet.slots) != width:
            raise OracleLineageError("packet width differs from slot exponent")
        edges = [edge for edge in packet.slots if edge is not None]
        if not edges:
            raise OracleLineageError("each packet must be nonempty")
        owned.extend(edges)
    if sorted(owned) != list(range(net.edges)):
        raise OracleLineageError("packet edge ownership is not exact and disjoint")
    if (len(packing.groups_left) != len(net.left)
            or len(packing.groups_right) != len(net.right)):
        raise OracleLineageError("packing labels do not match parent vertices")


def audit_child_oracle_lineage(
    parent: Network, packing: Packing, child: Network, *,
    group: int, coordinate: int, component: ChildComponent | None = None,
) -> ChildOracleLineage:
    """Check the *actual* direct/compiled child's inherited oracle identity.

    Retained vertices must be an exact, ordered subset of parent vertices,
    including identical Python callback references. Packet vertices must be
    PacketEntry objects, one per selected nonempty packet. The audit is
    deliberately strict about structure so a future source refactor cannot
    silently substitute a wrapper that copies inherited oracle state.
    """
    parent.validate()
    child.validate()
    _verify_parent_packing(parent, packing)
    if (type(group) is not int or type(coordinate) is not int
            or group < 0 or group >= packing.r
            or coordinate < 0 or coordinate >= packing.a):
        raise OracleLineageError("invalid packet group or coordinate")

    selected_kept = set(component.kept) if component is not None else None
    selected_packets = set(component.packets) if component is not None else None
    expected: list[Vertex] = []
    for side, vertices, labels in (
        ("Y", parent.left, packing.groups_left),
        ("X", parent.right, packing.groups_right),
    ):
        for index, vertex in enumerate(vertices):
            if (labels[index][coordinate] == group
                    and (selected_kept is None or (side, index) in selected_kept)):
                expected.append(vertex)

    packet_ids = [
        index for index in range(len(packing.packets))
        if selected_packets is None or index in selected_packets
    ]
    if len(child.left) != len(expected):
        raise OracleLineageError("inherited vertex count differs from retained sources")
    for old, new in zip(expected, child.left):
        if new.oracle is not old.oracle:
            raise OracleLineageError("inherited callback identity was changed")
        if new.name != old.name or len(new.ports) != len(old.ports):
            raise OracleLineageError("retained vertex label or degree was changed")

    if len(child.right) != len(packet_ids):
        raise OracleLineageError("new packet vertex count differs from packet geometry")
    parent_oracles = tuple(v.oracle for v in parent.left + parent.right)
    for packet_id, vertex in zip(packet_ids, child.right):
        oracle = vertex.oracle
        if not isinstance(oracle, PacketEntry):
            raise OracleLineageError("new packet vertex must own a PacketEntry")
        if oracle.packet_id != packet_id:
            raise OracleLineageError("packet identity does not match retained topology")
        if vertex.name != f"packet:{packet_id}:g{group}":
            raise OracleLineageError("packet vertex name differs from constructor")
        # Direct fields are finite coefficient data and local context; they
        # cannot be a reified parent Network or a direct parent callback.
        if any(value is parent or any(value is old for old in parent_oracles)
               for value in vars(oracle).values()):
            raise OracleLineageError("packet captured a parent oracle or Network")
    visible = len(child.left) + len(child.right)
    if visible > len(parent.left) + len(parent.right) + len(packing.packets):
        raise OracleLineageError("child exceeds parent-plus-packet vertex ceiling")
    return ChildOracleLineage(
        parent_vertices=len(parent.left) + len(parent.right),
        inherited_vertices=len(child.left),
        inherited_packet_vertices=sum(
            isinstance(v.oracle, PacketEntry) for v in child.left),
        new_packet_vertices=len(child.right),
        packet_count=len(packing.packets),
        child_vertices=visible,
    )
