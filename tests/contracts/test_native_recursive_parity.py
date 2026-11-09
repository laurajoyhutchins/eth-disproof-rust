"""Native recursive kernels must agree with the Python reference and policies."""
from __future__ import annotations

import random
from itertools import product
from types import SimpleNamespace

import pytest

from non_exponential_sudoku import ContractionEngine, ContractorConfig, LeafConfig, RecursionConfig
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.network import compile_leaf_plan, eliminate_leaf, simple_network
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = [pytest.mark.checkpoint, pytest.mark.requires_native]


def _network(edges: int, rng: random.Random):
    groups: list[list[list[int]]] = []
    for _ in range(2):
        parts: list[list[int]] = []
        for edge in range(edges):
            if parts and rng.randrange(3):
                parts[rng.randrange(len(parts))].append(edge)
            else:
                parts.append([edge])
        groups.append(parts)

    def factors(parts: list[list[int]]):
        return [(tuple(part), {
            bits: rng.choice((-3, -1, 0, 1, 2, 7))
            for bits in product((0, 1), repeat=len(part))
        }) for part in parts]

    return simple_network(edges, factors(groups[0]), factors(groups[1]))


@pytest.mark.parametrize("jet_degree", (0, 3))
@pytest.mark.parametrize("lookup_budget", (0, 8192))
def test_native_compiled_leaf_matches_independent_direct(
        jet_degree: int, lookup_budget: int) -> None:
    native = pytest.importorskip("native_recursive")
    rng = random.Random(98135 + jet_degree * 31 + lookup_budget)
    base = Padic(3, modulus_polynomial(3), 17)
    ring = JetRing(base, jet_degree) if jet_degree else base
    for _ in range(24):
        edges = rng.randint(1, 5)
        net = _network(edges, rng)
        scopes = tuple(v.ports for v in net.left + net.right)
        plan = compile_leaf_plan(edges, scopes, lookup_budget=lookup_budget)
        assert plan is not None
        expected = net.direct(ring, 5)
        assert eliminate_leaf(net, ring, 5, plan=plan) == expected
        assert native.eliminate_leaf(
            net, ring, 5, plan=plan, max_factor_bytes=16 * 1024 * 1024
        ) == expected
        assert native.eliminate_leaf(
            net, ring, 5, max_factor_bytes=16 * 1024 * 1024
        ) == expected


def test_native_leaf_refuses_same_budget_and_stale_plan() -> None:
    native = pytest.importorskip("native_recursive")
    ring = Padic(3, modulus_polynomial(3), 9)
    net = _network(4, random.Random(401))
    scopes = tuple(v.ports for v in net.left + net.right)
    plan = compile_leaf_plan(net.edges, scopes, lookup_budget=0)
    assert plan is not None
    assert all(step.lookup is None for step in plan.steps)
    for compiled in (None, plan):
        with pytest.raises(CapacityError, match="Leaf factor memory budget"):
            native.eliminate_leaf(net, ring, 4, plan=compiled, max_factor_bytes=1)
        with pytest.raises(ValueError, match="Leaf factor memory budget"):
            native.eliminate_leaf(net, ring, 4, plan=compiled, max_factor_bytes=0)
    with pytest.raises(ValueError, match="does not match"):
        native.eliminate_leaf(net, ring, 4, max_width=2, plan=plan)
    with pytest.raises(CapacityError, match="limit"):
        native.eliminate_leaf(net, ring, 3, plan=plan)


def test_native_leaf_engine_honors_custom_resources() -> None:
    pytest.importorskip("native_recursive")
    rng = random.Random(100)
    net = _network(2, rng)
    config = ContractorConfig(
        2, 9, schedule="micro",
        leaf=LeafConfig(
            strategy="eliminate", micro_threshold=2,
            max_width=2, lookup_entries=0, max_factor_bytes=1 << 20,
        ),
        recursion=RecursionConfig(native_leaf=True),
    )
    expected = net.direct(Padic(5, modulus_polynomial(5), 9), 2)[0]
    assert ContractionEngine(config).contract(net)[0] == expected


def test_native_zero_target_packet_including_source_tiles() -> None:
    native = pytest.importorskip("native_recursive")
    ring = Padic(3, modulus_polynomial(3), 11)
    row = ((0, ring.scalar(3)),)
    tile = ((SimpleNamespace(b=1), 1, ((0, 2),)),)
    # First bit is left assignment, second the right slot.
    for bits, expected in (
        ((1, 1), ring.scalar(6)),
        ((0, 1), ring.scalar(-4)),
        ((1, 0), ring.zero),
    ):
        got = native.packet_evaluate(
            bits, ring, (0,), (row,), ((),), (), tile, ((0, 1),)
        )
        assert got == expected
