"""A valid certificate need not preserve ORIGINAL clause components inside a group.

Finite algebraic counterexample to the invalid within-group factorization.
The documented measurement-separation identity only separates WHOLE
variable groups at a fixed measurement signature. It remains correct here.
"""
from __future__ import annotations

from fractions import Fraction

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, MeasurementDesign, ReplacementForm, ReplacementSystem,
    certify_measurements, deformation_polynomial, taylor_coefficients_separated,
)
from non_exponential_sudoku.eth.polynomial import ONE, ZERO, Polynomial


def _certified_disconnected_units() -> tuple[
    CNFFormula, ReplacementSystem, MeasurementDesign,
]:
    # Two independent original unit clauses. Variables 3 and 4 are
    # declared but unused, providing a second (free) group.
    formula = CNFFormula(4, ((1,), (2,)))
    t_over_two = Polynomial((Fraction(0), Fraction(1, 2)))
    replacements = ReplacementSystem((
        (ReplacementForm((ONE, t_over_two, ZERO, ZERO)),),
        (ReplacementForm((t_over_two, ONE, ZERO, ZERO)),),
    ))
    replacements.validate(formula)
    design = MeasurementDesign(
        groups=((0, 1), (2, 3)),
        clause_groups=(0, 0),
        matrices=((), ()), tau=Fraction(0), D=0,
    )
    # No cross-group coefficients, so all design conditions hold with
    # no measurements. This does NOT claim the source spectral
    # constructor produced these hand-specified replacement rows.
    certify_measurements(formula, replacements, design, at=1)
    return formula, replacements, design


def _local_weight(
    replacements: ReplacementSystem, x1: int, x2: int, *,
    center: int,
) -> Fraction:
    bits = (x1, x2, 0, 0)
    factors = []
    for forms in replacements.clauses:
        occurrence = forms[0]
        factors.append(sum(
            (poly.evaluate(center) * bit for poly, bit in zip(
                occurrence.coefficients, bits
            )), Fraction(0),
        ))
    return factors[0] * factors[1]


@pytest.mark.checkpoint
def test_valid_certificate_does_not_imply_original_component_factorization() -> None:
    formula, replacements, design = _certified_disconnected_units()
    assert formula.clauses == ((1,), (2,))
    assert all(not rows for rows in design.matrices)
    certificate = certify_measurements(
        formula, replacements, design, at=1,
    )
    assert certificate.total_measurements == 0
    # Distinct original components x1 and x2 become coupled by
    # perfectly legal within-group polynomial replacement rows.
    table = tuple(tuple(_local_weight(replacements, x1, x2, center=1)
                        for x2 in (0, 1)) for x1 in (0, 1))
    assert table == (
        (Fraction(0), Fraction(1, 2)),
        (Fraction(1, 2), Fraction(9, 4)),
    )
    determinant = table[0][0] * table[1][1] - table[0][1] * table[1][0]
    assert determinant == Fraction(-1, 4)
    # If W(x1,x2)=f(x1)g(x2), this determinant would be zero.
    # Therefore a generic split into original-clause components is FALSE.


@pytest.mark.integration
def test_whole_group_measurement_separation_remains_exact_despite_coupling() -> None:
    formula, replacements, design = _certified_disconnected_units()
    oracle = deformation_polynomial(formula, replacements)
    for center in (0, 1, 2):
        for order in (0, 1, 2):
            observed = taylor_coefficients_separated(
                formula, design, replacements, at=center, order=order,
                summation="tuples",
            )
            expected = oracle.taylor(center, order).coefficients
            expected += (Fraction(0),) * (order + 1 - len(expected))
            assert observed.coefficients == expected


@pytest.mark.checkpoint
def test_at_origin_original_components_do_factor() -> None:
    _, replacements, _ = _certified_disconnected_units()
    table = tuple(tuple(_local_weight(replacements, x1, x2, center=0)
                        for x2 in (0, 1)) for x1 in (0, 1))
    assert table == (
        (Fraction(0), Fraction(0)), (Fraction(0), Fraction(1))
    )
    assert table[0][0] * table[1][1] == table[0][1] * table[1][0]
