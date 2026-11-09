"""Canonical zero needs no arithmetic in a compiled exact leaf."""
from __future__ import annotations

from random import Random

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.network import (
    Network, Vertex, compile_leaf_plan, eliminate_leaf, simple_network,
)

pytestmark = pytest.mark.checkpoint


def test_leaf_skips_only_canonical_zero_addends() -> None:
    # This exact integer ring exposes the redundant operation directly.
    # Its canonical zero is a stable value, so identity is meaningful.
    from non_exponential_sudoku.core.network import _execute_leaf_plan

    class CountRing:
        zero = 0
        one = 1
        zero_adds = 0

        def add(self, left: int, right: int) -> int:
            if right is self.zero:
                self.zero_adds += 1
            return left + right

        def mul(self, left: int, right: int) -> int:
            return left * right

        def scalar(self, n: int) -> int:
            return n

    plan = compile_leaf_plan(1, ((0,), (0,)))
    assert plan is not None
    ring = CountRing()
    # First factor permits only bit zero, second factor permits both.
    assert _execute_leaf_plan(plan, {0: (1, 0), 1: (1, 1)}, ring) == 1
    assert ring.zero_adds == 0


@pytest.mark.parametrize('seed', [12, 44, 91])
def test_compiled_zero_shortcut_preserves_exhaustive_counts(seed: int) -> None:
    rng = Random(seed)
    ring = Padic(4, modulus_polynomial(4), 7)
    for edges in (1, 2, 3, 4):
        left = {(tuple((j >> i) & 1 for i in range(edges))):
                    rng.choice((0, 0, 1, 2, 3, -1)) for j in range(1 << edges)}
        right = {(tuple((j >> i) & 1 for i in range(edges))):
                    rng.choice((0, 0, 1, 2, 3, -2)) for j in range(1 << edges)}
        net = simple_network(edges, [(tuple(range(edges)), left)],
                                   [(tuple(range(edges)), right)])
        plan = compile_leaf_plan(edges,
            tuple(v.ports for v in net.left + net.right))
        assert plan is not None
        assert eliminate_leaf(net, ring, 8, plan=plan) == net.direct(ring, 8)


def test_noncanonical_vertex_outputs_still_normalize() -> None:
    ring = Padic(3, modulus_polynomial(3), 7)

    def noncanonical(bits: tuple[int, ...], R: Padic):
        return (1 + (1 << R.p), 0, 0) if bits[0] else (0, 0, 0)

    def unit(bits: tuple[int, ...], R: Padic):
        return R.one

    net = Network([Vertex('noncanonical', (0,), noncanonical)],
                  [Vertex('unit', (0,), unit)], 1)
    net.validate()
    plan = compile_leaf_plan(1, ((0,), (0,)))
    assert plan is not None
    assert eliminate_leaf(net, ring, 5, plan=plan) == net.direct(ring, 5) == ring.one
