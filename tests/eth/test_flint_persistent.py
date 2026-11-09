"""Real FLINT 0.9.0: persistent internal jets and exact boundary contracts."""
from __future__ import annotations

from fractions import Fraction
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, MeasurementDesign, Polynomial, ReplacementForm,
    ReplacementSystem, deformation_polynomial, restricted_taylor_sum,
    taylor_coefficients_separated,
)
from non_exponential_sudoku.eth.taylor import TaylorLimits, _JetArithmetic
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def _design(formula: CNFFormula) -> MeasurementDesign:
    middle = (formula.nvars + 1) // 2
    groups = (tuple(range(middle)), tuple(range(middle, formula.nvars)))
    matrices = tuple(tuple(tuple(int(i == j) for i in range(len(group)))
                           for j in range(len(group))) for group in groups)
    return MeasurementDesign(groups, tuple(j % 2 for j in range(len(formula.clauses))),
                             matrices, Fraction(1), 1)


def test_persistent_flint_jets_convert_only_at_public_boundary(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pytest.importorskip('flint')
    import non_exponential_sudoku.eth.taylor as taylor

    formula = CNFFormula(2, ((1, -2),))
    expected = taylor_coefficients_separated(formula, _design(formula), at=1, order=2)
    original = taylor._coefficients
    converted = 0

    def measured_conversion(poly: object) -> tuple[Fraction, ...]:
        nonlocal converted
        converted += 1
        return original(poly)

    monkeypatch.setattr(taylor, '_coefficients', measured_conversion)
    actual = taylor_coefficients_separated(formula, _design(formula), at=1,
                                           order=2, backend='flint')
    assert actual.coefficients == expected.coefficients
    assert actual.stats == expected.stats
    # The group sums and inclusion-exclusion remain native from start to finish.
    assert converted == 1
    converted = 0
    restricted = restricted_taylor_sum(formula, _design(formula), at=1,
                                       E=(0,), U=(0,), order=2, backend='flint')
    assert restricted.coefficients == restricted_taylor_sum(
        formula, _design(formula), at=1, E=(0,), U=(0,), order=2).coefficients
    assert converted == 1


def test_persistent_flint_randomized_rational_deformations() -> None:
    pytest.importorskip('flint')
    rng = Random(20261108)
    for _ in range(45):
        nvars = rng.randint(1, 3)
        clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, nvars)
                              for _ in range(rng.randint(0, 3)))
                        for _ in range(rng.randint(0, 3)))
        formula = CNFFormula(nvars, clauses)
        original = ReplacementSystem.identity(formula)
        replacements = ReplacementSystem(tuple(tuple(ReplacementForm(tuple(
            poly + Polynomial((0, Fraction(rng.randint(-2, 2), 7),
                               Fraction(rng.randint(-1, 1), 5)))
            for poly in form.coefficients)) for form in forms)
            for forms in original.clauses))
        design = _design(formula)
        center = Fraction(rng.choice((-2, -1, 1, 2)), rng.choice((1, 3)))
        order = rng.randint(0, 3)
        reference = taylor_coefficients_separated(formula, design, replacements,
                                                   at=center, order=order)
        native = taylor_coefficients_separated(formula, design, replacements,
                                                at=center, order=order, backend='flint')
        direct = deformation_polynomial(formula, replacements).taylor(center, order)
        assert native.coefficients == reference.coefficients == direct.coefficients + (
            Fraction(0),) * (order + 1 - len(direct.coefficients))
        assert native.stats == reference.stats


def test_persistent_flint_preserves_intermediate_capacity_refusals() -> None:
    pytest.importorskip('flint')
    for backend in ('python', 'flint'):
        arithmetic = _JetArithmetic(TaylorLimits(max_coefficient_bits=4), backend)
        big = arithmetic.constant(15, 2)
        with pytest.raises(CapacityError, match='coefficient bit limit'):
            arithmetic.add(big, arithmetic.constant(1, 2))
        with pytest.raises(CapacityError, match='coefficient bit limit'):
            arithmetic.mul(big, arithmetic.variable(Fraction(3), 2))

        exhausted = _JetArithmetic(TaylorLimits(max_jet_operations=2), backend)
        with pytest.raises(CapacityError, match='jet operation limit'):
            exhausted.mul(exhausted.variable(Fraction(2), 2),
                          exhausted.variable(Fraction(3), 2))


def test_persistent_flint_truncation_order_and_fraction_boundary() -> None:
    pytest.importorskip('flint')
    for backend in ('python', 'flint'):
        arithmetic = _JetArithmetic(TaylorLimits(), backend)
        x = arithmetic.variable(Fraction(1, 3), 2)
        cube = arithmetic.mul(arithmetic.mul(x, x), x)
        assert cube.full_coefficients() == (
            Fraction(1, 27), Fraction(1, 3), Fraction(1),
        )
        assert isinstance(cube.full_coefficients()[0], Fraction)
        with pytest.raises(ValueError, match='jet orders must match'):
            arithmetic.add(x, arithmetic.constant(1, 1))
