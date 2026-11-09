"""Native ETH arithmetic stays in FLINT until public exact-value export."""
from __future__ import annotations

from fractions import Fraction
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, HermiteDatum, Polynomial, ReplacementForm, ReplacementSystem,
    deformation_polynomial, interpolate_hermite,
)
from non_exponential_sudoku.eth.interpolation import HermiteLimits
from non_exponential_sudoku.eth.polynomial import ReferenceLimits
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def _full_taylor(polynomial: Polynomial, center: Fraction, order: int) -> tuple[Fraction, ...]:
    coeffs = polynomial.taylor(center, order).coefficients
    return coeffs + (Fraction(0),) * (order + 1 - len(coeffs))


def test_flint_polynomials_export_once_per_complete_calculation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pytest.importorskip('flint')
    import non_exponential_sudoku.eth.backends as backends

    original = backends._coefficients
    exports = 0

    def counted(value: object) -> tuple[Fraction, ...]:
        nonlocal exports
        exports += 1
        return original(value)

    monkeypatch.setattr(backends, '_coefficients', counted)
    formula = CNFFormula(3, ((1, -2), (2, 3)))
    identity = ReplacementSystem.identity(formula)
    perturbed = ReplacementSystem(tuple(tuple(ReplacementForm(tuple(
        polynomial + Polynomial((0, Fraction(index + 1, 7)))
        for index, polynomial in enumerate(form.coefficients)))
        for form in row) for row in identity.clauses))
    native = deformation_polynomial(formula, perturbed, backend='flint')
    assert exports == 1
    assert native == deformation_polynomial(formula, perturbed, backend='python')

    data = tuple(HermiteDatum(center, _full_taylor(native, center, native.degree))
                 for center in (Fraction(-2, 3), Fraction(1, 5)))
    recovered = interpolate_hermite(data, degree_bound=native.degree, backend='flint')
    assert recovered.polynomial == native
    assert exports == 2  # One export from each entire calculation.


def test_flint_hermite_matches_python_stats_with_zero_polynomial_and_mixed_orders() -> None:
    pytest.importorskip('flint')
    rng = Random(20261109)
    for _ in range(50):
        degree = rng.randint(0, 7)
        expected = Polynomial(tuple(Fraction(rng.randint(-9, 9), rng.randint(1, 7))
                                    for _ in range(degree + 1)))
        centers = rng.sample((Fraction(-2, 3), Fraction(-1), Fraction(1, 5), Fraction(2, 7)), 3)
        orders = [rng.randint(0, 3) for _ in centers]
        while sum(order + 1 for order in orders) <= degree:
            orders[rng.randrange(3)] += 1
        data = tuple(HermiteDatum(center, _full_taylor(expected, center, order))
                     for center, order in zip(centers, orders))
        reference = interpolate_hermite(data, degree_bound=degree)
        native = interpolate_hermite(data, degree_bound=degree, backend='flint')
        assert native.polynomial == reference.polynomial == expected
        assert native.stats == reference.stats


def test_native_and_reference_refuse_the_same_budget_exhaustion() -> None:
    pytest.importorskip('flint')
    data = (HermiteDatum(Fraction(1), (Fraction(3), Fraction(2), Fraction(1))),)
    for backend in ('python', 'flint'):
        with pytest.raises(CapacityError, match='rational operation limit'):
            interpolate_hermite(data, degree_bound=2, backend=backend,
                                limits=HermiteLimits(max_operations=2))
        with pytest.raises(CapacityError, match='coefficient bit limit'):
            interpolate_hermite((HermiteDatum(Fraction(1), (Fraction(1 << 40),)),),
                                degree_bound=0, backend=backend,
                                limits=HermiteLimits(max_coefficient_bits=8))
        replacement = ReplacementSystem(((ReplacementForm((Polynomial((1, 1 << 40)),)),),))
        with pytest.raises(CapacityError, match='coefficient bit limit'):
            deformation_polynomial(CNFFormula(1, ((1,),)), replacements=replacement,
                                   backend=backend,
                                   limits=ReferenceLimits(max_coefficient_bits=8))


def test_large_exact_rationals_never_use_string_round_trips() -> None:
    pytest.importorskip('flint')
    from non_exponential_sudoku.eth.backends import _from_flint, _q, require_flint

    flint = require_flint()
    value = Fraction((1 << 513) + 7, (1 << 511) + 11)
    assert _from_flint(_q(value, flint)) == value
    assert isinstance(_from_flint(_q(value, flint)), Fraction)
