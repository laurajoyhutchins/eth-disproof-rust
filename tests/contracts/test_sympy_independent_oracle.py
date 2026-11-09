"""Independent mathematical-library equivalence, optional at checkout time."""
from __future__ import annotations

import random

import pytest

pytest.importorskip("sympy")

from non_exponential_sudoku.core.algebra import Padic, irreducible_mod_two, modulus_polynomial
from research.sympy_oracle import SympyRingOracle, irreducible_mod_two as external_irreducible


@pytest.mark.checkpoint
@pytest.mark.parametrize("degree,precision", [(2, 1), (3, 7), (5, 17), (6, 65), (8, 129)])
def test_exact_quotient_ring_matches_sympy(degree: int, precision: int) -> None:
    ring = Padic(degree, modulus_polynomial(degree), precision)
    oracle = SympyRingOracle(ring)
    rng = random.Random(4100 + degree * 100 + precision)
    modulus = 1 << precision
    for _ in range(12):
        # Include noncanonical coefficients and negative representatives.
        a = tuple(rng.randrange(-modulus, modulus * 2) for _ in range(degree))
        b = tuple(rng.randrange(-modulus, modulus * 2) for _ in range(degree))
        assert ring.add(a, b) == oracle.add(a, b)
        assert ring.sub(a, b) == oracle.sub(a, b)
        assert ring.mul(a, b) == oracle.mul(a, b)
        assert ring.pow(a, 3) == oracle.pow(a, 3)
        # Verification of the inverse uses independent polynomial multiplication.
        if any(v & 1 for v in a):
            assert oracle.mul(a, ring.inv(a)) == ring.one


@pytest.mark.checkpoint
@pytest.mark.parametrize("degree", range(2, 10))
def test_irreducible_selection_against_sympy(degree: int) -> None:
    selected = modulus_polynomial(degree)
    assert external_irreducible(selected, degree)
    for lower in range(1, selected & ((1 << degree) - 1), 2):
        assert not external_irreducible((1 << degree) | lower, degree)
    for lower in range(1, 1 << degree, 2):
        candidate = (1 << degree) | lower
        assert irreducible_mod_two(candidate, degree) == external_irreducible(candidate, degree)
