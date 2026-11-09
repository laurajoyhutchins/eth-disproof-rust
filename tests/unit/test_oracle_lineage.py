"""Actual child vertices retain parent oracles; packet oracles are new leaves.

This is a *single recursive path* ownership theorem, NOT a proof that any
original arbitrary Python oracle is inexpensive or that total branch work is
subexponential. The audit is independent of the production constructor.
"""
from __future__ import annotations

from dataclasses import replace

import pytest

from non_exponential_sudoku.contraction.children import (
    child_components, compile_child, make_child,
)
from non_exponential_sudoku.contraction.packets import PacketEntry
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.network import Network, Vertex, simple_network
from non_exponential_sudoku.core.packing import Packet, pack
from reference.oracle_lineage import (
    OracleLineageError, audit_child_oracle_lineage,
    paper_single_path_descriptor_bound,
)

pytestmark = pytest.mark.checkpoint


def _source() -> Network:
    return simple_network(
        4,
        [([0, 1], {(0, 0): 1, (1, 1): 1}),
         ([2, 3], {(0, 0): 1, (1, 1): 1})],
        [([0, 2], {(0, 0): 1, (1, 1): 1}),
         ([1, 3], {(0, 0): 1, (1, 1): 1})],
    )


@pytest.mark.parametrize("compiled", [False, True])
def test_real_child_preserves_oracle_identity_and_adds_only_packets(compiled: bool) -> None:
    source = _source()
    packing = pack(source, 2, 1)
    ring = Padic(3, modulus_polynomial(3), 9)
    group = packing.groups_left[0][0]
    plan = compile_child(source, packing, group, 0) if compiled else None
    child = make_child(source, packing, [], (), 1, ring.one,
                       ring, group, 0, plan=plan)
    report = audit_child_oracle_lineage(source, packing, child,
                                       group=group, coordinate=0)
    assert report.inherited_vertices == len(child.left)
    assert report.new_packet_vertices == len(child.right)
    assert report.child_vertices <= report.parent_vertices + report.packet_count
    assert report.parent_vertices == len(source.left) + len(source.right)
    assert all(isinstance(v.oracle, PacketEntry) for v in child.right)
    assert all(any(v.oracle is old.oracle for old in source.left + source.right)
               for v in child.left)
    assert child.direct(ring, 12) == make_child(
        source, packing, [], (), 1, ring.one, ring, group, 0,
        plan=None if compiled else compile_child(source, packing, group, 0),
    ).direct(ring, 12)


def test_component_restriction_and_compiled_child_agree_on_oracle_ownership() -> None:
    source = _source()
    packing = pack(source, 2, 1)
    ring = Padic(3, modulus_polynomial(3), 9)
    group = packing.groups_left[0][0]
    parts = child_components(source, packing, group, 0)
    assert parts
    for part in parts:
        direct = make_child(source, packing, [], (), 1, ring.one,
                            ring, group, 0, component=part)
        plan = compile_child(source, packing, group, 0, component=part)
        prepared = make_child(source, packing, [], (), 1, ring.one,
                              ring, group, 0, component=part, plan=plan)
        for child in (direct, prepared):
            result = audit_child_oracle_lineage(
                source, packing, child, group=group, coordinate=0,
                component=part,
            )
            assert result.new_packet_vertices == len(part.packets)
            assert result.inherited_vertices == len(part.kept)
        assert direct.direct(ring, 12) == prepared.direct(ring, 12)


def test_second_generation_inherits_packet_oracle_without_wrapping_it() -> None:
    source = _source()
    ring = Padic(3, modulus_polynomial(3), 9)
    packing = pack(source, 2, 1)
    first = make_child(source, packing, [], (), 1, ring.one, ring,
                       packing.groups_left[0][0], 0)
    assert first.right
    packing2 = pack(first, 2, 1)
    inherited_packet_index = 0
    group = packing2.groups_right[inherited_packet_index][0]
    second = make_child(first, packing2, [], (), 1, ring.one, ring,
                        group, 0)
    result = audit_child_oracle_lineage(
        first, packing2, second, group=group, coordinate=0,
    )
    original_packet = first.right[inherited_packet_index].oracle
    assert isinstance(original_packet, PacketEntry)
    assert any(v.oracle is original_packet for v in second.left)
    assert all(v.oracle is not original_packet for v in second.right)
    assert result.child_vertices <= result.parent_vertices + result.packet_count
    bound = paper_single_path_descriptor_bound(
        root_edges=source.edges,
        root_vertices=len(source.left) + len(source.right),
    )
    # These are micro-geometry tests of source identity. They are NOT
    # admitted paper-schedule executions, so only the one-step bound applies.
    assert bound.max_vertices >= len(source.left) + len(source.right)


def test_forged_inherited_callback_cannot_pass_the_audit() -> None:
    source = _source()
    packing = pack(source, 2, 1)
    ring = Padic(3, modulus_polynomial(3), 9)
    group = packing.groups_left[0][0]
    child = make_child(source, packing, [], (), 1, ring.one, ring, group, 0)
    assert child.left
    copied = Network(
        [Vertex(v.name, v.ports, lambda bits, R: R.one) if j == 0 else v
         for j, v in enumerate(child.left)],
        list(child.right), child.edges,
    )
    with pytest.raises(OracleLineageError, match="identity"):
        audit_child_oracle_lineage(source, packing, copied,
                                   group=group, coordinate=0)


def test_forged_packet_oracle_cannot_pass_the_audit() -> None:
    source = _source()
    packing = pack(source, 2, 1)
    ring = Padic(3, modulus_polynomial(3), 9)
    group = packing.groups_left[0][0]
    child = make_child(source, packing, [], (), 1, ring.one, ring, group, 0)
    assert child.right
    forged = Network(
        list(child.left),
        [Vertex(v.name, v.ports, source.left[0].oracle) if j == 0 else v
         for j, v in enumerate(child.right)],
        child.edges,
    )
    with pytest.raises(OracleLineageError, match="PacketEntry"):
        audit_child_oracle_lineage(source, packing, forged,
                                   group=group, coordinate=0)


def test_packet_count_requires_nonempty_disjoint_source_edge_ownership() -> None:
    source = _source()
    packing = pack(source, 2, 1)
    ring = Padic(3, modulus_polynomial(3), 9)
    group = packing.groups_left[0][0]
    child = make_child(source, packing, [], (), 1, ring.one, ring, group, 0)
    packing.packets.append(Packet(tuple(None for _ in range(2)), ((0, 0),)))
    with pytest.raises(OracleLineageError, match="nonempty"):
        audit_child_oracle_lineage(source, packing, child,
                                   group=group, coordinate=0)


def test_single_path_paper_bound_sums_all_future_packet_descriptors() -> None:
    for root_edges in range(0, 300):
        bound = paper_single_path_descriptor_bound(
            root_edges=root_edges, root_vertices=13,
        )
        remaining = root_edges
        sum_packets = 0
        while remaining:
            sum_packets += remaining
            remaining = 3 * remaining // 32
        assert sum_packets <= bound.max_new_packet_descriptors
        assert bound.max_new_packet_descriptors == 32 * root_edges // 29
        assert bound.max_vertices == 13 + bound.max_new_packet_descriptors
        assert bound.applies_only_to_successful_paper_shrinkage
    with pytest.raises(ValueError):
        paper_single_path_descriptor_bound(root_edges=-1, root_vertices=3)
    with pytest.raises(ValueError):
        paper_single_path_descriptor_bound(root_edges=3, root_vertices=-1)
    with pytest.raises(ValueError):
        paper_single_path_descriptor_bound(root_edges=3.0, root_vertices=1)  # type: ignore[arg-type]
