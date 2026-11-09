"""Exact stress cases for native ring and prepared packet arithmetic."""
from __future__ import annotations

import random
from itertools import product
from types import SimpleNamespace

import pytest

from non_exponential_sudoku.core import algebra as alg
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.network import (
    compile_leaf_plan, eliminate_leaf, estimated_coefficient_bytes, simple_network,
)
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = (pytest.mark.checkpoint, pytest.mark.requires_native)


@pytest.mark.parametrize("extension_degree", [2, 5, 12, 32])
@pytest.mark.parametrize("precision", [1, 7, 63, 129, 521])
def test_native_ring_scalar_and_square_exact_with_noncanonical_coordinates(
    extension_degree: int, precision: int, monkeypatch: pytest.MonkeyPatch,
) -> None:
    native = pytest.importorskip("native_ring")
    rng = random.Random(1234567 + extension_degree * 701 + precision)
    ring = Padic(extension_degree, modulus_polynomial(extension_degree), precision)
    mask = ring.mask
    zero = (0,) * extension_degree
    one = (1,) + (0,) * (extension_degree - 1)
    for _ in range(6):
        a = tuple(rng.randrange(1 << precision) for _ in range(extension_degree))
        b = tuple(rng.randrange(1 << precision) for _ in range(extension_degree))
        # Include values beyond canonical representatives; native fast paths
        # must normalize rather than returning an input tuple unchanged.
        lifted = tuple(x + ((rng.randrange(4) - 2) << precision) for x in a)
        scalar = (rng.randrange(1 << precision),) + zero[1:]
        variants = (
            (a, b), (a, a), (lifted, lifted),
            (a, scalar), (scalar, b),
            (one, lifted), (zero, b),
            ((1 << precision,) + zero[1:], lifted),
        )
        with monkeypatch.context() as patch:
            patch.setattr(alg, "_native_ring", None)
            expected = [ring.mul(x, y) for x, y in variants]
        actual = [native.mul(x, y, ring.e, ring.f, mask) for x, y in variants]
        assert actual == expected


@pytest.mark.parametrize("desired", [(), (1,), (2, 1), (513,)])
def test_prepared_packet_uses_bit_positions_without_slot_conversion(
    desired: tuple[int, ...],
) -> None:
    native = pytest.importorskip("native_recursive")
    ring = Padic(3, modulus_polynomial(3), 17)
    mode = SimpleNamespace(b=2)
    row_slots = (((4, ring.scalar(3)), (1, ring.scalar(7))),)
    row_bits = (((2, ring.scalar(3)), (3, ring.scalar(7))),)
    right_positions = ((4, 2), (1, 3))
    tile_slots = ((mode, 2, ((4, 2), (1, 5))),)
    tile_bits = ((mode, 2, ((2, 2), (3, 5))),)
    contributions = (tuple((i, ring.scalar(i + 2)) for i in range(len(desired))),)
    for bits in product((0, 1), repeat=4):
        original = native.packet_evaluate(
            bits, ring, (0,), row_slots, contributions, desired,
            tile_slots, right_positions,
        )
        prepared = native.packet_evaluate(
            bits, ring, (0,), row_bits, contributions, desired,
            tile_bits, right_positions, positions_are_bits=True,
        )
        assert prepared == original


def test_compiled_leaf_live_table_budget_matches_reference_at_boundaries() -> None:
    native = pytest.importorskip("native_recursive")
    ring = Padic(4, modulus_polynomial(4), 19)
    net = simple_network(
        4,
        [((0, 1), {(0, 0): 1, (1, 1): 2}),
         ((2, 3), {(0, 1): 3, (1, 0): 4})],
        [((0, 2), {(0, 1): 5, (1, 0): 6}),
         ((1, 3), {(0, 0): 7, (1, 1): 8})],
    )
    scopes = tuple(v.ports for v in net.left + net.right)
    width = 4
    answer = net.direct(ring, 4)
    coefficient_bytes = estimated_coefficient_bytes(ring)
    for lookup_budget in (0, 8192):
        plan = compile_leaf_plan(net.edges, scopes, max_width=width,
                                 lookup_budget=lookup_budget)
        assert plan is not None
        for permitted_entries in (1, 3, 4, 7, 8, 12, 16, 32):
            max_bytes = coefficient_bytes * permitted_entries
            def reference() -> object:
                return eliminate_leaf(
                    net, ring, 4, max_width=width, plan=plan,
                    max_factor_bytes=max_bytes,
                )
            def compiled_native() -> object:
                return native.eliminate_leaf(
                    net, ring, 4, max_width=width, plan=plan,
                    max_factor_bytes=max_bytes,
                )
            try:
                result = reference()
            except CapacityError:
                with pytest.raises(CapacityError, match="Leaf factor memory"):
                    compiled_native()
            else:
                assert result == answer
                assert compiled_native() == result
