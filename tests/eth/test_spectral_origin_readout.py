"""Independent exact checks for spectral compression and origin-only Hermite recovery."""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from random import Random

import pytest

from non_exponential_sudoku.eth.construction import (
    _interpolation_polynomial, _walsh_coefficients,
)
from non_exponential_sudoku.eth.interpolation import (
    HermiteDatum, HermiteLimits, interpolate_hermite, interpolate_origin_hermite,
)
from non_exponential_sudoku.eth.polynomial import Polynomial
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize("start,R", [(0, 1), (1, 2), (3, 4), (6, 6), (10, 8)])
def test_integer_valued_newton_interpolation_matches_lagrange(start: int, R: int) -> None:
    """The Newton representation agrees with an independent Lagrange oracle."""
    points = tuple(range(start, start + R))
    actual = _interpolation_polynomial(points)
    expected = Polynomial.constant(0)
    for t in points:
        basis = Polynomial.constant(1)
        for u in points:
            if u != t:
                basis = (basis * Polynomial((-u, 1))).scale(Fraction(1, t - u))
        expected = expected + basis.scale((-1) ** t)
    assert actual == expected
    assert actual.degree <= R - 1
    for t in points:
        assert actual.evaluate(t) == (-1) ** t


@pytest.mark.parametrize("Q,R", [(3, 2), (4, 3), (5, 2), (6, 4), (7, 3)])
def test_cardinality_walsh_matches_independent_cube(Q: int, R: int) -> None:
    polynomial = _interpolation_polynomial(tuple(range(1, R + 1)))
    compressed = _walsh_coefficients(polynomial, Q)
    for mask in range(1 << Q):
        original = sum(
            (polynomial.evaluate(index.bit_count()) *
             (-1 if (index & mask).bit_count() % 2 else 1)
             for index in range(1 << Q)), Fraction(0),
        ) / (1 << Q)
        assert compressed.get(mask, Fraction(0)) == original
        if mask.bit_count() >= R:
            assert original == 0


@pytest.mark.parametrize("centers_orders", [
    ((1, 3), (2, 3)),
    ((-2, 2), (1, 3), (Fraction(3, 2), 2)),
    ((1, 4), (2, 4), (3, 4)),
    ((-1, 3), (1, 2), (2, 4), (3, 3)),
])
def test_direct_hermite_origin_matches_full_polynomial(
    centers_orders: tuple[tuple[int | Fraction, int], ...],
) -> None:
    rng = Random(4021)
    conditions = sum(order for _, order in centers_orders)
    for trial in range(3):
        degree = conditions - 1 - trial
        polynomial = Polynomial(tuple(
            Fraction(rng.randrange(-13, 14), rng.randrange(1, 12))
            for _ in range(degree + 1)
        ))
        data = []
        for center, order in centers_orders:
            shifted = polynomial.taylor(center, order - 1).coefficients
            data.append(HermiteDatum(Fraction(center),
                                     shifted + (Fraction(0),) * (order - len(shifted))))
        full = interpolate_hermite(data, degree_bound=conditions - 1)
        origin = interpolate_origin_hermite(data)
        assert origin.value == full.polynomial.at_zero == polynomial.at_zero
        assert origin.stats.total_conditions == conditions
        assert origin.stats.centers == len(data)


def test_origin_only_rejects_bad_centers_and_respects_bit_budget() -> None:
    with pytest.raises(ValueError, match='distinct'):
        interpolate_origin_hermite([HermiteDatum(Fraction(1), (1,)),
                                    HermiteDatum(Fraction(1), (2,))])
    with pytest.raises(ValueError, match='center'):
        interpolate_origin_hermite([])
    with pytest.raises(CapacityError, match='bit'):
        interpolate_origin_hermite(
            [HermiteDatum(Fraction(2), (1 << 120,))],
            limits=HermiteLimits(max_coefficient_bits=40),
        )


def test_single_center_origin_uses_only_its_taylor_jet() -> None:
    polynomial = Polynomial((Fraction(7, 3), Fraction(-5, 2), Fraction(3, 7)))
    jet = polynomial.taylor(Fraction(5, 2), 2).coefficients
    result = interpolate_origin_hermite([HermiteDatum(Fraction(5, 2), jet)])
    assert result.value == polynomial.at_zero


def test_constructed_counter_matches_original_full_readout() -> None:
    from non_exponential_sudoku.eth import (
        CNFFormula, construct_bounded_designs, count_bruteforce,
        count_from_constructed,
    )

    formulas = (
        CNFFormula(3, ((1, -2), (-1, 3), (2, 3))),
        CNFFormula(3, ((1, 2),)),
        CNFFormula(3, ()),
        CNFFormula(3, ((),)),
    )
    for formula in formulas:
        designs = construct_bounded_designs(formula, r=2, Q=2, R=2)
        assert count_from_constructed(formula, designs) == count_from_constructed(
            formula, designs, readout='polynomial',
        ) == count_bruteforce(formula)
    with pytest.raises(ValueError, match='readout'):
        count_from_constructed(formulas[0], construct_bounded_designs(
            formulas[0], r=2, Q=2, R=2), readout='unknown')  # type: ignore[arg-type]
