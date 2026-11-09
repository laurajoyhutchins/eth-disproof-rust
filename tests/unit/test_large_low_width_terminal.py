"""Large low-width PAPER leaves complete without relaxing exhaustive safety bounds.

This is a non-refusal increment for a bounded structural family, *not* a
universal totality or subexponential worst-case proof.
"""
from __future__ import annotations

from collections.abc import Mapping

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.network import (
    Network, compile_leaf_plan, eliminate_leaf, simple_network,
)
from non_exponential_sudoku.contraction.engine import ContractionEngine
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.runtime.config import ContractorConfig, LeafConfig

pytestmark = pytest.mark.checkpoint


def independent_edge_network(n: int) -> Network:
    one: Mapping[tuple[int, ...], int] = {(0,): 1, (1,): 1}
    left: list[tuple[tuple[int, ...], Mapping[tuple[int, ...], int]]] = [
        ((i,), one) for i in range(n)
    ]
    right: list[tuple[tuple[int, ...], Mapping[tuple[int, ...], int]]] = [
        ((i,), one) for i in range(n)
    ]
    return simple_network(n, left, right)


@pytest.mark.parametrize("edges", [19, 48, 96])
@pytest.mark.parametrize("compiled", [False, True])
def test_low_width_leaf_completes_past_exhaustive_edge_limit(edges: int, compiled: bool) -> None:
    net = independent_edge_network(edges)
    ring = Padic(3, modulus_polynomial(3), edges + 1)
    if compiled:
        plan = compile_leaf_plan(
            net.edges, tuple(v.ports for v in net.left + net.right),
            max_width=2, lookup_budget=4096,
        )
        assert plan is not None
    else:
        plan = None
    assert eliminate_leaf(net, ring, max_edges=18, max_width=2,
                          plan=plan, max_factor_bytes=4 * 1024 * 1024) == ring.scalar(1 << edges)
    # The exponential reference is intentionally disallowed at this size.
    with pytest.raises(CapacityError, match="Direct leaf"):
        net.direct(ring, 18)


def test_inactive_paper_schedule_uses_structural_elimination() -> None:
    net = independent_edge_network(26)
    engine = ContractionEngine(ContractorConfig(
        s=net.edges, precision=net.edges + 1, schedule="paper",
        leaf=LeafConfig(strategy="eliminate", limit=18),
    ))
    result = engine.contract(net)
    assert result == Padic(engine.e, engine.f, net.edges + 1).scalar(1 << net.edges)
    assert engine.stats.active_paper_calls == 0
    assert engine.stats.leaves == 1


def test_wide_leaf_never_silently_uses_unbounded_exhaustive_fallback() -> None:
    edges = 21
    all_ones: Mapping[tuple[int, ...], int] = {(0,) * edges: 1}
    unary: Mapping[tuple[int, ...], int] = {(0,): 1, (1,): 1}
    net = simple_network(
        edges, [(tuple(range(edges)), all_ones)],
        [((i,), unary) for i in range(edges)],
    )
    ring = Padic(3, modulus_polynomial(3), 24)
    with pytest.raises(CapacityError, match="Direct leaf"):
        eliminate_leaf(net, ring, max_edges=18, max_width=2, max_factor_bytes=1024*1024)


def test_large_low_width_leaf_still_honors_memory_limit() -> None:
    net = independent_edge_network(48)
    ring = Padic(3, modulus_polynomial(3), 49)
    with pytest.raises(CapacityError, match="memory budget"):
        eliminate_leaf(net, ring, max_edges=18, max_width=2, max_factor_bytes=100)


def test_connected_cycle_low_width_leaf_completes_above_limit() -> None:
    edges = 32
    # Alternating pair factors form a connected cycle in the factor graph.
    # Every assignment is valid, so the exact count is 2**edges.
    pair_ones: Mapping[tuple[int, ...], int] = {
        (0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): 1
    }
    left: list[tuple[tuple[int, ...], Mapping[tuple[int, ...], int]]] = [
        ((i, i + 1), pair_ones) for i in range(0, edges, 2)
    ]
    right: list[tuple[tuple[int, ...], Mapping[tuple[int, ...], int]]] = [
        (((i + 1) % edges, (i + 2) % edges), pair_ones)
             for i in range(0, edges, 2)]
    net = simple_network(edges, left, right)
    ring = Padic(3, modulus_polynomial(3), edges + 1)
    assert eliminate_leaf(net, ring, max_edges=18, max_width=2,
                          max_factor_bytes=4 * 1024 * 1024) == ring.scalar(1 << edges)


def test_large_leaf_without_memory_ceiling_refuses_before_evaluating_oracles() -> None:
    net = independent_edge_network(32)
    ring = Padic(3, modulus_polynomial(3), 33)
    with pytest.raises(CapacityError, match="explicit factor-memory budget"):
        eliminate_leaf(net, ring, max_edges=18, max_width=2)
