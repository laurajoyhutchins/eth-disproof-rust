"""Small, independent mathematical witnesses for the normalized formulas."""
from fractions import Fraction
from math import comb

import pytest

from non_exponential_sudoku.contraction.packets import (
    cauchy_values,
    cross_mode_coefficient,
)
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial, v2
from non_exponential_sudoku.recovery.hermite import tapered_recover
from non_exponential_sudoku.recovery.streaming import StreamingHermite
from reference.paper_algebra import cauchy_kernel, eval_poly

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize("L", [2, 4])
def test_cauchy_unit_normalization_matches_independent_rational_kernel(L):
    """Only the *units* are inverted; compare with Q-polynomials directly."""
    ring = Padic(5, modulus_polynomial(5), 16)
    for center in range(-L, L):
        for scalar in (0, 1, 3):
            z = ring.scalar(scalar)
            coefficients = cauchy_values(center, z, ring, L)
            argument = center + 2 * L * scalar
            # A packet has x,y in [0,L), hence |y-x| < L.
            for displacement in range(1 - L, L):
                x = max(0, -displacement)
                y = x + displacement
                rational = eval_poly(cauchy_kernel(L, x, y), argument)
                assert coefficients[displacement] == ring.rational(rational)


@pytest.mark.parametrize("L", [2, 4])
def test_cross_mode_coefficients_vanish_without_deformation(L):
    ring = Padic(5, modulus_polynomial(5), 11)
    for center in range(-L, L):
        if not center:
            continue
        for x in range(L):
            for y in range(L):
                displacement = center - y + x
                if displacement == 0 or v2(displacement) > v2(center):
                    continue
                for order in (0, 1, 2):
                    assert cross_mode_coefficient(
                        center, ring.zero, ring, L, x, y, order
                    ) == ring.zero


@pytest.mark.parametrize("M,L,u", [(1, 2, 1), (2, 2, 2), (2, 4, 1)])
def test_eager_and_streaming_hermite_recover_polynomial_constant(M, L, u):
    """Each center supplies Taylor data from the same integer polynomial."""
    base = Padic(4, modulus_polynomial(4), 8)
    polynomial = (3, -2, 1)  # F(X) = 3 - 2X + X^2
    accumulator = StreamingHermite(M, L, u, base)
    center_jets = {}
    for center, order in accumulator.qs.items():
        if order == 0:
            continue
        lifted = Padic(base.e, base.f, accumulator.precision(center))
        coefficients = []
        for degree in range(order):
            taylor = sum(
                polynomial[j] * comb(j, degree)
                * accumulator.alpha**degree * center**(j - degree)
                for j in range(degree, len(polynomial))
            )
            coefficients.append(lifted.scalar(taylor))
        center_jets[center] = coefficients

    for center in reversed(tuple(center_jets)):
        accumulator.add_center(center, center_jets[center])
    assert accumulator.finish() == base.scalar(polynomial[0])
    assert tapered_recover(center_jets, M, L, u, base.p, base.e, base.f) == base.scalar(3)


def test_eager_hermite_requires_every_active_center():
    base = Padic(3, modulus_polynomial(3), 7)
    accumulator = StreamingHermite(1, 2, 1, base)
    center = next(t for t, order in accumulator.qs.items() if order)
    lifted = Padic(base.e, base.f, accumulator.precision(center))
    with pytest.raises(ValueError, match="Missing Hermite centers"):
        tapered_recover(
            {center: [lifted.zero] * accumulator.qs[center]},
            1, 2, 1, base.p, base.e, base.f,
        )

@pytest.mark.parametrize("L", [2, 4, 8])
def test_center_reuses_cauchy_product_for_cross_modes(L):
    """Center-local cross coefficients agree with independent standalone evaluation."""
    from non_exponential_sudoku.contraction.packets import EvaluationContext
    ring = Padic(5, modulus_polynomial(5), 13)
    for center in (-L, -1, 1, L - 1):
        for z in (ring.scalar(3), ring.basis(2)):
            context = EvaluationContext(center, z, ring, L.bit_length() - 1)
            assert context.cauchy == cauchy_values(center, z, ring, L)
            assert context._cauchy_product == context.cauchy[center]
            for x, y0 in ((0, 0), (0, L - 1), (L - 1, 0), (L - 1, L - 1)):
                difference = center - y0 + x
                if difference == 0 or v2(difference) > v2(center):
                    continue
                for exponent in (0, 1, 3):
                    assert context.cross_coefficient(x, y0, exponent) == (
                        cross_mode_coefficient(center, z, ring, L, x, y0, exponent)
                    )


def test_center_reuse_across_dense_and_lazy_jets():
    """Sharing the product preserves exact Taylor jets and optional laziness."""
    from non_exponential_sudoku.contraction.packets import EvaluationContext
    from non_exponential_sudoku.core.jets import JetRing
    base = Padic(4, modulus_polynomial(4), 9)
    ring = JetRing(base, 3)
    for center in (-1, 1):
        for lazy in (False, True):
            context = EvaluationContext(
                center, ring.variable, ring, 2,
                packet_coeff_cache_limit=16 if lazy else None,
            )
            result = context.cross_coefficient(0, 0, 1)
            if lazy:
                assert context.lazy_ring is not None
                result = context.lazy_ring.materialize(result)
            assert result == cross_mode_coefficient(
                center, ring.variable, ring, 4, 0, 0, 1,
            )
