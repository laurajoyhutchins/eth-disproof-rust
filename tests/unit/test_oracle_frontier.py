"""One-assignment oracle-frontier TDD on real recursively constructed children.

These are structural, not a complete bit complexity or non-refusal theorem.
"""
from __future__ import annotations

from itertools import product

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing, embed_element
from non_exponential_sudoku.core.network import Network, simple_network
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.contraction.children import make_child
from non_exponential_sudoku.contraction.packets import PacketEntry
from reference.oracle_frontier import (
    UncertifiedOracle, certify_oracle_frontier, inherited_oracle_identity,
    lift_work_envelope, ring_shape,
)

pytestmark = pytest.mark.checkpoint


def _network() -> Network:
    ones = {bits: 1 for bits in product((0, 1), repeat=2)}
    return simple_network(
        4,
        [([0, 1], ones), ([2, 3], ones)],
        [([0, 2], ones), ([1, 3], ones)],
    )


def _two_generations() -> tuple[Network, Network, Network, Padic]:
    parent = _network()
    ring = Padic(3, modulus_polynomial(3), 7)
    current = parent
    out = [parent]
    for _ in range(2):
        packing = pack(current, 2, 1)
        modes = mode_catalog(current, packing, 1, ring.p)
        candidates = [make_child(
            current, packing, modes, (0,) * len(modes),
            1, ring.one, ring, group, 0,
        ) for group in (0, 1)]
        current = max(candidates, key=lambda net: net.edges)
        current.validate()
        out.append(current)
    return out[0], out[1], out[2], ring


def test_two_children_inherit_objects_without_wrapping_original_oracles() -> None:
    original, child, grandchild, _ = _two_generations()
    assert inherited_oracle_identity(original, child)
    assert inherited_oracle_identity(child, grandchild)
    assert all(isinstance(v.oracle, PacketEntry) for v in child.right)
    assert any(isinstance(v.oracle, PacketEntry) for v in grandchild.left)
    assert len(grandchild.left) + len(grandchild.right) <= (
        len(original.left) + len(original.right)
        + len(child.right) + len(grandchild.right)
    )
    # Proof deliberately excludes source/oracle retention & cache RSS.


def test_oracle_frontier_refuses_unbounded_input_oracles() -> None:
    original, child, grandchild, ring = _two_generations()
    for graph in (original, child, grandchild):
        with pytest.raises(UncertifiedOracle, match='input oracle'):
            certify_oracle_frontier(graph, ring)


def test_per_assignment_oracle_frontier_is_additive_not_recursive() -> None:
    original, child, grandchild, ring = _two_generations()
    all_base_costs = {id(v.oracle): 1 for v in original.left + original.right}
    counts = [certify_oracle_frontier(graph, ring, input_oracle_costs=all_base_costs)
              for graph in (original, child, grandchild)]
    assert counts[0].packet_vertices == 0
    assert counts[1].packet_vertices > 0
    assert counts[2].packet_vertices > 0
    for graph, count in zip((original, child, grandchild), counts):
        assert count.total_vertices == count.packet_vertices + count.input_vertices
        assert count.input_oracle_cost_sum == count.input_vertices
        assert count.packet_ring_call_ceiling >= 0
    # One inherited packet is evaluated as one vertex, not a recursive
    # invocation of every oracle in its creation-time parent network.
    assert counts[2].packet_vertices == sum(
        isinstance(v.oracle, PacketEntry) for v in grandchild.left + grandchild.right
    )


def test_packet_evaluation_does_not_call_another_packet_oracle(monkeypatch: pytest.MonkeyPatch) -> None:
    _, _, grandchild, ring = _two_generations()
    requested = Padic(ring.e, ring.f, ring.p + 4)
    expected = grandchild.direct(requested, 4)
    original_call = PacketEntry.__call__
    stack = [0, 0, 0]

    def traced(self: PacketEntry, bits: tuple[int, ...], target: Padic) -> object:
        stack[0] += 1
        stack[1] = max(stack[1], stack[0])
        stack[2] += 1
        try:
            return original_call(self, bits, target)
        finally:
            stack[0] -= 1

    monkeypatch.setattr(PacketEntry, '__call__', traced)
    assert grandchild.direct(requested, 4) == expected
    assert stack[1] == 1
    assert stack[2] > 0


def test_precision_lift_counts_exact_coordinate_mask_visits(monkeypatch: pytest.MonkeyPatch) -> None:
    r = Padic(3, modulus_polynomial(3), 9)
    source = JetRing(JetRing(r, 2), 3)
    target = JetRing(JetRing(JetRing(Padic(3, r.f, 15), 2), 3), 4)
    value = source.one
    envelope = lift_work_envelope(source, target)
    assert ring_shape(source).scalar_coordinates == 18
    assert envelope.scalar_coordinate_masks == 18
    assert envelope.source_tuple_nodes == 1 + 3 + 6
    assert envelope.extra_jet_tuple_nodes == 1
    assert envelope.extra_zero_tail_references == 3
    seen = [0]
    old_lift = Padic.lift

    def traced(self: Padic, coords: object) -> tuple[int, ...]:
        seen[0] += 1
        return old_lift(self, coords)  # type: ignore[arg-type]

    monkeypatch.setattr(Padic, 'lift', traced)
    output = embed_element(value, source, target)
    assert output[1:] == target.zero[1:]
    assert seen[0] * r.e == envelope.scalar_coordinate_masks


def test_invalid_lift_shapes_and_assumed_oracle_costs_are_refused() -> None:
    r = Padic(3, modulus_polynomial(3), 9)
    different = Padic(3, r.f, 8)
    with pytest.raises(ValueError, match='nondecreasing'):
        lift_work_envelope(r, different)
    with pytest.raises(ValueError, match='incompatible'):
        lift_work_envelope(JetRing(r, 2), JetRing(different, 3))
    original, _, _, _ = _two_generations()
    bounds = {id(v.oracle): 1 for v in original.left + original.right}
    key = next(iter(bounds))
    bounds[key] = -2
    with pytest.raises(UncertifiedOracle):
        certify_oracle_frontier(original, r, input_oracle_costs=bounds)
