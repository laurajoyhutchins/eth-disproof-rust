"""ETH-003: independently certified measurement separation and exact sums."""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, MeasurementDesign, Polynomial, ReplacementForm,
    ReplacementSystem, SeparatedLimits, certify_measurements,
    count_bruteforce, deformation_polynomial, evaluate_separated,
)
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def design_two_variables() -> MeasurementDesign:
    return MeasurementDesign(
        groups=((0,), (1,)), clause_groups=(0,),
        matrices=((), ((1,),)), tau=Fraction(1, 2), D=1,
    )


def test_empty_conjunction_empty_clause_and_unconstrained_variables() -> None:
    empty = MeasurementDesign(((),), (), ((),), Fraction(0), 0)
    assert evaluate_separated(CNFFormula(0, ()), empty).value == 1
    contradiction = replace(empty, clause_groups=(0,))
    assert evaluate_separated(CNFFormula(0, ((),)), contradiction).value == 0

    formula = CNFFormula(4, ((1,),))
    design = MeasurementDesign(((0, 1), (2, 3)), (0,), ((), ()), Fraction(0), 0)
    result = evaluate_separated(formula, design)
    assert result.value == 8 == count_bruteforce(formula)
    assert result.stats.measurement_tuples == 1
    assert result.stats.group_assignments_tried == 8  # 4+4, not 16


def test_cross_group_measurements_have_exact_rational_witnesses() -> None:
    formula = CNFFormula(4, ((1, -3), (2, 4)))
    design = MeasurementDesign(
        ((0, 1), (2, 3)), (0, 1),
        (((1, 1), (1, -1)), ((1, 1), (1, -1))),
        Fraction(1, 2), 2,
    )
    identity = ReplacementSystem.identity(formula)
    rows: list[tuple[ReplacementForm, ...]] = []
    for e, forms in enumerate(identity.clauses):
        transformed: list[ReplacementForm] = []
        for form in forms:
            additions = (Fraction(0), Fraction(0), Fraction(1, 2), Fraction(-3, 4)) if e == 0 else (
                Fraction(1, 3), Fraction(-2, 5), Fraction(0), Fraction(0)
            )
            coefficients = tuple(poly + Polynomial.variable().scale(delta)
                                 for poly, delta in zip(form.coefficients, additions))
            transformed.append(ReplacementForm(coefficients))
        rows.append(tuple(transformed))
    replacements = ReplacementSystem(tuple(rows))
    cert = certify_measurements(formula, replacements, design, at=1)
    assert cert.total_measurements == 4
    assert cert.occurrences[0][0].lambda_by_group[1] == (Fraction(-1, 8), Fraction(5, 8))
    assert cert.occurrences[1][0].lambda_by_group[0] == (Fraction(7, 15), Fraction(-2, 15))
    for t in (Fraction(0), Fraction(1), Fraction(-3, 2), Fraction(5, 3)):
        result = evaluate_separated(formula, design, replacements, at=t)
        assert result.value == deformation_polynomial(formula, replacements).evaluate(t)
        assert result.stats.measurement_tuples == 5 ** 4
        assert result.stats.max_coefficient_bits > 0


def test_negative_measurement_values_and_redundant_rows() -> None:
    formula = CNFFormula(2, ((1, 2),))
    design = MeasurementDesign(
        ((0,), (1,)), (0,), ((), ((-1,), (-1,))),
        Fraction(1), 1,
    )
    cert = certify_measurements(formula, ReplacementSystem.identity(formula), design, at=2)
    assert cert.occurrences[0][1].lambda_by_group[1] == (Fraction(-1), Fraction(0))
    result = evaluate_separated(formula, design, at=2)
    assert result.value == 3
    assert result.stats.measurement_tuples == 9
    assert result.stats.group_assignments_matching > 0


def test_design_must_be_certified_at_each_center() -> None:
    formula = CNFFormula(2, ((1,),))
    # Cross-group term vanishes at t=1 but not at t=2.
    cross = Polynomial((Fraction(0), Fraction(-1), Fraction(1)))
    adapted = ReplacementSystem(((ReplacementForm((Polynomial.constant(1), cross)),),))
    no_measurements = replace(design_two_variables(), matrices=((), ()), tau=Fraction(0))
    assert evaluate_separated(formula, no_measurements, adapted, at=1).value == (
        deformation_polynomial(formula, adapted).evaluate(1)
    )
    with pytest.raises(ValueError, match='row space'):
        certify_measurements(formula, adapted, no_measurements, at=2)


@pytest.mark.parametrize('mutation,match', [
    (dict(groups=((0,), (0,))), 'partition'),
    (dict(groups=((0,), (2,))), 'variable index'),
    (dict(groups=((0, 1), (), ()), matrices=((), (), ())), 'small-group'),
    (dict(clause_groups=()), 'assigned group'),
    (dict(clause_groups=(2,)), 'assigned group'),
    (dict(matrices=((), ((1, 0),))), 'width'),
    (dict(matrices=((), ((2,),))), 'L1'),
    (dict(matrices=((), ((Fraction(1, 2),),))), 'integers'),
    (dict(matrices=((), ((True,),))), 'integers'),
    (dict(tau=Fraction(0)), '2\\*tau\\*n'),
    (dict(tau=Fraction(-1)), 'tau'),
    (dict(tau=0.5), 'exact'),
    (dict(D=-1), 'D'),
    (dict(D=True), 'D'),
])
def test_bad_designs_refuse_before_evaluation(mutation: dict[str, object], match: str) -> None:
    formula = CNFFormula(2, ((1, 2),))
    design = replace(design_two_variables(), **mutation)
    with pytest.raises((TypeError, ValueError), match=match):
        evaluate_separated(formula, design)


def test_missing_measurement_direction_and_bad_replacement_refuse() -> None:
    formula = CNFFormula(2, ((1, 2),))
    identity = ReplacementSystem.identity(formula)
    with pytest.raises(ValueError, match='row space'):
        evaluate_separated(formula, replace(design_two_variables(), matrices=((), ()), tau=Fraction(0)))
    swapped = ReplacementSystem(((identity.clauses[0][1], identity.clauses[0][0]),))
    with pytest.raises(ValueError, match='original'):
        evaluate_separated(formula, design_two_variables(), swapped)
    with pytest.raises(TypeError, match='exact'):
        evaluate_separated(formula, design_two_variables(), at=0.5)  # type: ignore[arg-type]


def test_capacity_limits_fail_closed_with_no_fallback() -> None:
    formula = CNFFormula(2, ((1, 2),))
    design = design_two_variables()
    with pytest.raises(CapacityError, match='variable'):
        evaluate_separated(formula, design, limits=SeparatedLimits(max_variables=1))
    with pytest.raises(CapacityError, match='tuple'):
        evaluate_separated(formula, design, limits=SeparatedLimits(max_measurement_tuples=2))
    with pytest.raises(CapacityError, match='group assignment'):
        evaluate_separated(formula, design, limits=SeparatedLimits(max_group_assignments=10))
    with pytest.raises(CapacityError, match='operation'):
        evaluate_separated(formula, design, limits=SeparatedLimits(max_operations=1))
    identity = ReplacementSystem.identity(formula)
    enormous = Polynomial((0, 1 << 30))
    modified = ReplacementSystem(((identity.clauses[0][0], ReplacementForm((
        enormous, identity.clauses[0][1].coefficients[1],
    ))),))
    # One cross-group measurement is still not enough to hide an input at zero:
    # enormous has constant 0 so the replacement remains valid.
    with pytest.raises(CapacityError, match='bit'):
        evaluate_separated(formula, design, modified, limits=SeparatedLimits(max_coefficient_bits=12))
    with pytest.raises(ValueError):
        SeparatedLimits(max_measurement_tuples=0)


def test_randomized_cross_group_deformations_against_direct_polynomial() -> None:
    rng = Random(20261025)
    for _ in range(48):
        n = rng.randint(1, 5)
        split = (n + 1) // 2
        groups = (tuple(range(split)), tuple(range(split, n)))
        # Shared measurements have small signed coefficients and are rank
        # deficient when a group has more than one variable.
        # Flatten one measurement row per nonempty group.
        measurements = tuple(((tuple((-1) ** i for i in group)),) if group else () for group in groups)
        clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randint(0, 3)))
                        for _ in range(rng.randint(0, 3)))
        formula = CNFFormula(n, clauses)
        ownership = tuple(rng.randrange(2) for _ in formula.clauses)
        design = MeasurementDesign(groups, ownership, measurements, Fraction(1), max(1, split))
        center = rng.choice((Fraction(1), Fraction(-2, 3), Fraction(2)))
        replacements: list[tuple[ReplacementForm, ...]] = []
        for e, clause in enumerate(formula.clauses):
            forms: list[ReplacementForm] = []
            for literal in clause:
                local_slopes = [Fraction(rng.randint(-2, 2), 3) for _ in range(n)]
                for h, group in enumerate(groups):
                    if h != ownership[e] and group:
                        multiplier = Fraction(rng.randint(-3, 3), 4)
                        for j, index in enumerate(group):
                            local_slopes[index] = (multiplier * measurements[h][0][j]
                                                   - int(index == abs(literal) - 1)) / center
                forms.append(ReplacementForm(tuple(Polynomial((
                    int(index == abs(literal) - 1), local_slopes[index]
                )) for index in range(n))))
            replacements.append(tuple(forms))
        system = ReplacementSystem(tuple(replacements))
        direct = deformation_polynomial(formula, system)
        assert direct.at_zero == count_bruteforce(formula)
        result = evaluate_separated(formula, design, system, at=center)
        assert result.value == direct.evaluate(center)
