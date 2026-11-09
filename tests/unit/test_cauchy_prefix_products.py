"""Independent quadratic reference for the linear prefix/suffix identity."""

import pytest

from non_exponential_sudoku.contraction.packets import cauchy_values
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial, v2
from non_exponential_sudoku.core.jets import JetRing

pytestmark = pytest.mark.checkpoint


def quadratic_weights(t, z, ring, L):
    """Reference constructed directly from the original exclusion products."""
    alpha = 2 * L
    denominator = 1
    for q in range(-L, L):
        if q:
            denominator *= -q
    inverse = ring.inv(ring.scalar(denominator >> v2(denominator)))
    result = {}
    for delta in range(-L, L):
        weight = inverse
        for q in range(-L, L):
            if q == t or q == delta:
                continue
            difference = t - q
            valuation = v2(difference)
            factor = ring.add(ring.scalar(difference >> valuation),
                              ring.mul(ring.scalar(alpha >> valuation), z))
            weight = ring.mul(weight, factor)
        if delta != t:
            valuation = v2(t - delta)
            weight = ring.mul(weight, ring.mul(ring.scalar(alpha >> valuation), z))
        result[delta] = weight
    return result


@pytest.mark.parametrize("L", [2, 4, 8, 16])
def test_prefix_products_equal_quadratic_formula_with_zero_factors(L):
    ring = Padic(4, modulus_polynomial(4), 11)
    for t in (-L, -1, 1, L - 1, L + 1):
        for z in (ring.zero, ring.scalar(1), ring.basis(2)):
            assert cauchy_values(t, z, ring, L) == quadratic_weights(t, z, ring, L)


def test_prefix_products_preserve_nested_jet_arithmetic():
    base = Padic(4, modulus_polynomial(4), 9)
    ring = JetRing(base, 3)
    for t in (-2, -1, 1, 2):
        assert cauchy_values(t, ring.variable, ring, 4) == (
            quadratic_weights(t, ring.variable, ring, 4)
        )
