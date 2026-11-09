"""Source-backed proof of target-degree zero before building recursive children.

The certificate is exact even for native and lazy packet evaluations because
it concerns the coefficient's polynomial degree, not the implementation.
"""
from __future__ import annotations

from dataclasses import replace
from itertools import product

import pytest

from non_exponential_sudoku import ContractionEngine, ContractorConfig
from non_exponential_sudoku.contraction.child_evaluator import ChildEvaluator
from non_exponential_sudoku.contraction.children import ChildComponent, make_child
from non_exponential_sudoku.contraction.packet_degree import (
    impossible_packet_target_degree, packet_target_row_capacity,
)
from non_exponential_sudoku.contraction.packets import EvaluationContext, PacketEntry
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.modes import Mode, mode_catalog, weighted_tuples
from non_exponential_sudoku.core.network import simple_network
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.runtime.config import RecursionConfig
from non_exponential_sudoku.sudoku.encoding import port_graph_with_cross_mode

pytestmark = pytest.mark.checkpoint


def _case() -> tuple[object, object, list[Mode], tuple[Mode, Mode],
                     Padic, int, int]:
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    ring = Padic(5, modulus_polynomial(5), 19)
    catalog = mode_catalog(net, packing, 1, ring.p)
    assert catalog
    first = catalog[0]
    other = next(
        (mode for mode in catalog if mode is not first
         and mode.packet == first.packet and mode.target == first.target),
        None,
    )
    if other is None:
        # Two distinct formal mode variables with the same valid packet,
        # group and row support. The packet coefficient is still a real
        # prepared polynomial; this is not a claim about paper admissibility.
        other = replace(first, b=first.b + 1, weight=first.weight + 1)
    cap = packet_target_row_capacity(net, packing, 0)
    row_count = cap[(first.packet, first.target)]
    assert row_count >= 1
    return net, packing, catalog, (first, other), ring, first.target, row_count


def test_parent_packet_rows_are_counted_exactly_once() -> None:
    net, packing, _, pair, _, group, rows = _case()
    capacity = packet_target_row_capacity(net, packing, 0)
    assert sum(capacity.values()) == net.edges
    assert capacity[(pair[0].packet, group)] == rows
    with pytest.raises(ValueError):
        packet_target_row_capacity(net, packing, packing.a)


def test_requested_degree_exceeding_available_rows_is_a_certificate() -> None:
    net, packing, _, pair, ring, group, rows = _case()
    cap = packet_target_row_capacity(net, packing, 0)
    betas = (rows, 1)
    witness = impossible_packet_target_degree(
        pair, betas, group=group, row_capacity=cap,
    )
    assert witness is not None
    assert witness.packet_id == pair[0].packet
    assert witness.requested_degree == rows + 1
    assert witness.available_rows == rows

    child = make_child(
        net, packing, list(pair), betas, 1, ring.one, ring,
        group, 0, EvaluationContext(1, ring.one, ring, 1),
    )
    packet_vertices = [
        v for v in child.right
        if isinstance(v.oracle, PacketEntry)
        and v.oracle.packet_id == witness.packet_id
    ]
    assert packet_vertices
    for vertex in packet_vertices:
        for bits in product((0, 1), repeat=len(vertex.ports)):
            assert vertex.oracle(bits, ring) == ring.zero


@pytest.mark.parametrize("compiled", [False, True])
def test_degree_certificate_precedes_child_construction(
    monkeypatch: pytest.MonkeyPatch, compiled: bool,
) -> None:
    import non_exponential_sudoku.contraction.child_evaluator as evaluator_module

    net, packing, _, pair, ring, group, rows = _case()
    contractor = ContractionEngine(ContractorConfig(
        net.edges, ring.p, schedule="micro",
        recursion=RecursionConfig(child_plans=compiled),
    ))
    evaluator = ChildEvaluator(
        contractor, net, packing, list(pair), 1, ring.one, ring,
        0, 0, EvaluationContext(1, ring.one, ring, 1),
    )

    def never_construct(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("zero packet must not allocate a child")

    monkeypatch.setattr(evaluator_module, "make_child", never_construct)
    with monkeypatch.context() as patch:
        from non_exponential_sudoku.contraction.compiled_children import CompiledChildPlan
        patch.setattr(CompiledChildPlan, "instantiate", never_construct)
        assert evaluator.evaluate(group, (rows, 1)) == ring.zero
    assert contractor.stats.packet_degree_zero_certificates == 1
    assert contractor.stats.child_networks == 0
    assert contractor.stats.child_cache_misses == 0
    assert contractor.stats.zero_support_attempts == 0


def test_no_false_certificate_for_source_modes_or_feasible_target() -> None:
    net, packing, _, pair, _, group, rows = _case()
    capacity = packet_target_row_capacity(net, packing, 0)
    assert impossible_packet_target_degree(
        pair, (1, 0), group=group, row_capacity=capacity,
    ) is None
    assert impossible_packet_target_degree(
        pair, (0, 0), group=group, row_capacity=capacity,
    ) is None
    other_group = 1-group
    assert impossible_packet_target_degree(
        pair, (rows, 1), group=other_group, row_capacity=capacity,
    ) is None
    assert impossible_packet_target_degree(
        pair, (rows, 1), group=group, row_capacity=capacity,
        component=ChildComponent((), ()),
    ) is None


def test_uncertified_mode_inputs_never_produce_a_false_zero() -> None:
    net, packing, _, pair, _, group, rows = _case()
    capacity = packet_target_row_capacity(net, packing, 0)
    with pytest.raises(ValueError, match="one multiplicity"):
        impossible_packet_target_degree(
            pair, (1,), group=group, row_capacity=capacity,
        )
    with pytest.raises(ValueError, match="nonnegative"):
        impossible_packet_target_degree(
            pair, (-1, 0), group=group, row_capacity=capacity,
        )
    with pytest.raises(ValueError, match="nonnegative"):
        impossible_packet_target_degree(
            pair, (True, 1), group=group, row_capacity=capacity,
        )
    bogus = replace(pair[0], packet=-1)
    assert impossible_packet_target_degree(
        (bogus, pair[1]), (rows, 1), group=group, row_capacity=capacity,
    ) is None


def test_two_distinct_genuine_catalog_modes_cannot_overfill_two_packet_rows() -> None:
    # Four-slot packet with both orientations present. Coordinate zero has
    # two target rows for group zero and distinct b=0 and b=1 source modes,
    # both produced by the real valuation-pruned mode catalog.
    tab = {(0,): 1, (1,): 1}
    net = simple_network(
        4,
        [((i,), tab) for i in range(4)],
        [((i,), tab) for i in range(4)],
    )
    labels = (
        ((0, 0), (1, 0), (0, 1), (1, 1)),
        ((1, 1), (0, 1), (1, 0), (0, 0)),
    )
    packing = pack(net, 2, 2, labels)
    assert len(packing.packets) == 1
    ring = Padic(5, modulus_polynomial(5), 19)
    modes = mode_catalog(net, packing, 1, ring.p)
    pair = next(
        ((a, d) for a in modes for d in modes
         if a is not d and a.packet == d.packet
         and a.target == d.target and a.b == 0 and d.b == 1),
        None,
    )
    assert pair is not None, "genuine catalog must contain two target modes"
    group = pair[0].target
    capacity = packet_target_row_capacity(net, packing, 0)
    assert capacity[(pair[0].packet, group)] == 2
    # Independently admissible: total valuation < precision and each
    # exponent <= target-row count.
    beta = (2, 1)
    assert sum(m.weight * b for m, b in zip(pair, beta)) < ring.p
    assert all(b <= len(m.rows) for m, b in zip(pair, beta))
    assert beta in set(weighted_tuples(list(pair), ring.p))
    witness = impossible_packet_target_degree(
        pair, beta, group=group, row_capacity=capacity,
    )
    assert witness is not None
    assert witness.requested_degree == 3 and witness.available_rows == 2

    child = make_child(
        net, packing, list(pair), beta, 1, ring.one, ring, group, 0,
        EvaluationContext(1, ring.one, ring, packing.a),
    )
    observed = 0
    for v in child.right:
        if isinstance(v.oracle, PacketEntry) and v.oracle.packet_id == pair[0].packet:
            for bits in product((0, 1), repeat=len(v.ports)):
                observed += 1
                assert v.oracle(bits, ring) == ring.zero
    assert observed > 0
