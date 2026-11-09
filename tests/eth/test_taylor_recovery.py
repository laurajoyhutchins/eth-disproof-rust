"""ETH-004: restricted Boolean differences, exact jets, and Hermite CRT."""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction
from math import comb
from random import Random

import pytest

from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
from non_exponential_sudoku.eth.design import MeasurementDesign
from non_exponential_sudoku.eth.interpolation import (
    HermiteDatum, HermiteLimits, count_from_manual_designs, interpolate_hermite,
)
from non_exponential_sudoku.eth.polynomial import (
    ONE, ZERO, Polynomial, ReplacementForm, ReplacementSystem,
    deformation_polynomial,
)
from non_exponential_sudoku.eth.taylor import (
    Jet, TaylorLimits, restricted_taylor_sum, taylor_coefficients_separated,
)
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def coordinate_design(formula: CNFFormula) -> MeasurementDesign:
    n = formula.nvars
    split = (n + 1) // 2
    groups = (tuple(range(split)), tuple(range(split, n))) if n else ((),)
    matrices = tuple(tuple(tuple(int(i == j) for i in range(len(group)))
                           for j in range(len(group))) for group in groups)
    return MeasurementDesign(groups, tuple(i % len(groups) for i in range(len(formula.clauses))),
                             matrices, Fraction(1), 1 if n else 0)


def transformed(formula: CNFFormula, slopes: tuple[int, ...]) -> ReplacementSystem:
    base = ReplacementSystem.identity(formula)
    clauses = []
    for rows in base.clauses:
        forms = []
        for form in rows:
            coeffs = tuple(poly + Polynomial((0, Fraction(slope, 3)))
                           for poly, slope in zip(form.coefficients, slopes))
            forms.append(ReplacementForm(coeffs))
        clauses.append(tuple(forms))
    return ReplacementSystem(tuple(clauses))


def reference_restricted(
    formula: CNFFormula, replacements: ReplacementSystem, at: Fraction,
    E: tuple[int, ...], U: tuple[int, ...], order: int,
) -> tuple[Fraction, ...]:
    """Independent full-cube oracle for Z(t,E,U); tests only, never production."""
    value = ZERO
    for mask in range(1 << formula.nvars):
        if any(not (mask & (1 << i)) for i in E):
            continue
        product = ONE
        for clause, rows in zip(formula.clauses, replacements.clauses):
            not_satisfied = ONE
            for literal, form in zip(clause, rows):
                base = sum((poly.evaluate(at) for i, poly in enumerate(form.coefficients)
                            if mask & (1 << i)), Fraction(0))
                delta = ZERO
                for index in U:
                    poly = form.coefficients[index]
                    delta += poly.taylor(at, order) - Polynomial.constant(poly.evaluate(at))
                linear = Polynomial.constant(base) + delta
                not_satisfied = (not_satisfied * (ONE - linear if literal > 0 else linear)).truncate(order)
            product = (product * (ONE - not_satisfied)).truncate(order)
        value = (value + product).truncate(order)
    return value.coefficients + (Fraction(0),) * (order + 1 - len(value.coefficients))


def test_jets_are_exact_truncated_and_refuse_rounded_inputs() -> None:
    a = Jet((Fraction(1, 3), Fraction(2), Fraction(5)), 2)
    b = Jet((Fraction(2, 3), Fraction(-1), Fraction(4)), 2)
    assert (a + b).full_coefficients() == (1, 1, 9)
    assert (a * b).full_coefficients() == (Fraction(2, 9), Fraction(1), Fraction(8, 3))
    assert (a - a).full_coefficients() == (0, 0, 0)
    assert Jet((), 0) == Jet.constant(0, 0)
    with pytest.raises(TypeError):
        Jet((0.5,), 1)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        Jet((1, 2, 3), 1)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        _ = a * Jet.constant(1, 1)


def test_restricted_sums_match_independent_boolean_cube() -> None:
    formula = CNFFormula(3, ((1, -2, 3), (-1, 2)))
    design = coordinate_design(formula)
    base = ReplacementSystem.identity(formula)
    replacements = ReplacementSystem(tuple(tuple(ReplacementForm(tuple(
        coefficient + Polynomial((0, Fraction(i - 1, 4), Fraction(i + 1, 7)))
        for i, coefficient in enumerate(form.coefficients))) for form in rows)
        for rows in base.clauses))
    for center in (Fraction(1), Fraction(-2, 3)):
        for order in (0, 1, 2, 3):
            for E, U in (((), ()), ((0,), ()), ((0,), (0,)),
                         ((0, 2), (2,)), ((0, 1, 2), (0, 2))):
                if len(E) > order:
                    continue
                result = restricted_taylor_sum(formula, design, replacements,
                                               at=center, E=E, U=U, order=order)
                expected = reference_restricted(formula, replacements, center, E, U, order)
                assert result.coefficients == expected
                assert result.stats.taylor_pairs == 1


def test_truncated_inclusion_exclusion_matches_direct_derivatives() -> None:
    formula = CNFFormula(3, ((1, -2, 3), (-1, 2)))
    replacements = transformed(formula, (2, -1, 3))
    direct = deformation_polynomial(formula, replacements)
    design = coordinate_design(formula)
    for center in (Fraction(1), Fraction(2, 3)):
        for order in range(4):
            result = taylor_coefficients_separated(formula, design, replacements,
                                                   at=center, order=order)
            expected = direct.taylor(center, order).coefficients
            assert result.coefficients == expected + (0,) * (order + 1 - len(expected))
            assert result.stats.taylor_pairs == sum(
                comb(formula.nvars, i) * 2 ** i
                for i in range(min(order, formula.nvars) + 1))


def test_randomized_differential_and_shifted_input_powers() -> None:
    rng = Random(20261025)
    for _ in range(25):
        n = rng.randint(1, 3)
        clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randint(0, 3)))
                        for _ in range(rng.randint(0, 3)))
        formula = CNFFormula(n, clauses)
        base = ReplacementSystem.identity(formula)
        system = ReplacementSystem(tuple(tuple(ReplacementForm(tuple(
            poly + Polynomial((0, Fraction(rng.randint(-2, 2), 5),
                               Fraction(rng.randint(-1, 1), 7)))
            for poly in form.coefficients)) for form in forms)
            for forms in base.clauses))
        direct = deformation_polynomial(formula, system)
        center = Fraction(rng.choice((-2, -1, 1, 2)), rng.choice((1, 3)))
        order = rng.randint(0, 3)
        result = taylor_coefficients_separated(formula, coordinate_design(formula), system,
                                               at=center, order=order)
        expected = direct.taylor(center, order).coefficients
        assert result.coefficients == expected + (0,) * (order + 1 - len(expected))
        assert direct.at_zero == count_bruteforce(formula)


def test_empty_conjunction_contradiction_unused_variables_and_order_zero() -> None:
    for formula in (CNFFormula(0, ()), CNFFormula(0, ((),)),
                    CNFFormula(2, ()), CNFFormula(2, ((),)), CNFFormula(3, ((1,),))):
        design = coordinate_design(formula)
        for order in (0, 1):
            result = taylor_coefficients_separated(formula, design, at=1, order=order)
            assert result.coefficients == (Fraction(count_bruteforce(formula)),) + (Fraction(0),) * order


def test_rational_hermite_with_mixed_jets_and_high_order() -> None:
    polynomial = Polynomial((Fraction(7, 3), Fraction(-4, 9), 0, Fraction(13, 11), -2))
    datum = []
    for center, length in ((Fraction(-1, 2), 2), (Fraction(2), 1), (Fraction(3, 2), 2)):
        shifted = polynomial.taylor(center, length - 1).coefficients
        datum.append(HermiteDatum(center, shifted + (0,) * (length - len(shifted))))
    result = interpolate_hermite(datum, degree_bound=4)
    assert result.polynomial == polynomial
    assert result.stats.centers == 3
    assert result.stats.total_conditions == 5

    # A q=0 path is ordinary interpolation from distinct nonzero centers.
    data_values = [HermiteDatum(Fraction(i), (polynomial.evaluate(i),)) for i in (1, 2, 3, 4, 5)]
    assert interpolate_hermite(data_values, degree_bound=4).polynomial == polynomial


def test_hermite_rejects_ambiguity_inconsistency_and_approximation() -> None:
    with pytest.raises(ValueError, match='insufficient'):
        interpolate_hermite([HermiteDatum(Fraction(1), (0,))], degree_bound=1)
    with pytest.raises(ValueError, match='distinct'):
        interpolate_hermite([HermiteDatum(Fraction(1), (0,)), HermiteDatum(Fraction(1), (1,))],
                            degree_bound=1)
    with pytest.raises(ValueError, match='inconsistent'):
        interpolate_hermite([HermiteDatum(Fraction(1), (0,)), HermiteDatum(Fraction(2), (1,))],
                            degree_bound=0)
    with pytest.raises(ValueError, match='nonzero'):
        HermiteDatum(Fraction(0), (1,))
    with pytest.raises(TypeError):
        HermiteDatum(Fraction(1), (0.5,))  # type: ignore[arg-type]
    with pytest.raises(ValueError, match='nonnegative'):
        interpolate_hermite([HermiteDatum(Fraction(1), (0,))], degree_bound=-1)


def test_count_manual_path_with_no_exhaustive_fallback(monkeypatch: pytest.MonkeyPatch) -> None:
    formula = CNFFormula(3, ((1, -2), (2, 3), (-1, 3)))
    base = ReplacementSystem.identity(formula)
    system = ReplacementSystem(tuple(tuple(ReplacementForm(tuple(
        poly + Polynomial((0, Fraction(i + 1, 5)))
        for i, poly in enumerate(form.coefficients))) for form in forms)
        for forms in base.clauses))
    degree_bound = sum(len(clause) for clause in formula.clauses)
    assert degree_bound == 6
    manual = [(Fraction(i), coordinate_design(formula)) for i in (1, 2, 3)]
    # Strictly more conditions than the verified upper bound.
    import non_exponential_sudoku.eth.cnf as cnf_module
    import non_exponential_sudoku.eth.polynomial as polynomial_module

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError('exhaustive reference oracle was used')

    expected = count_bruteforce(formula)
    monkeypatch.setattr(cnf_module, 'count_bruteforce', forbidden)
    monkeypatch.setattr(polynomial_module, 'deformation_polynomial', forbidden)
    result = count_from_manual_designs(formula, manual, system, order=2)
    assert result.count == expected
    assert result.polynomial.at_zero == expected
    assert len(result.taylor_data) == 3
    assert all(d.stats.taylor_pairs == 19 for d in result.taylor_data)


def test_restriction_and_capacity_fail_closed() -> None:
    formula = CNFFormula(2, ((1, -2),))
    design = coordinate_design(formula)
    with pytest.raises(ValueError, match='subset'):
        restricted_taylor_sum(formula, design, at=1, E=(0,), U=(1,), order=1)
    with pytest.raises(ValueError, match='sorted unique'):
        restricted_taylor_sum(formula, design, at=1, E=(0, 0), U=(), order=2)
    with pytest.raises(ValueError, match='must not exceed'):
        restricted_taylor_sum(formula, design, at=1, E=(0, 1), U=(), order=1)
    with pytest.raises(CapacityError, match='order'):
        taylor_coefficients_separated(formula, design, at=1, order=3,
                                      limits=TaylorLimits(max_taylor_order=2))
    with pytest.raises(CapacityError, match='pair'):
        taylor_coefficients_separated(formula, design, at=1, order=1,
                                      limits=TaylorLimits(max_taylor_pairs=2))
    with pytest.raises(CapacityError, match='measurement tuple'):
        taylor_coefficients_separated(formula, design, at=1, order=1,
                                      limits=TaylorLimits(max_measurement_tuples=2))
    with pytest.raises(CapacityError, match='group assignment'):
        taylor_coefficients_separated(formula, design, at=1, order=1,
                                      limits=TaylorLimits(max_group_assignments=2))
    with pytest.raises(CapacityError, match='operation'):
        taylor_coefficients_separated(formula, design, at=1, order=0,
                                      limits=TaylorLimits(max_jet_operations=1))
    huge = ReplacementSystem(((ReplacementForm((Polynomial((1, 1 << 30)), ZERO)),
                               ReplacementForm((ZERO, ONE))),))
    with pytest.raises(CapacityError, match='bit'):
        taylor_coefficients_separated(formula, design, huge, at=1, order=1,
                                      limits=TaylorLimits(max_coefficient_bits=10))
    with pytest.raises(CapacityError, match='bit'):
        interpolate_hermite([HermiteDatum(Fraction(1), (1 << 100,))], degree_bound=0,
                            limits=HermiteLimits(max_coefficient_bits=10))
    with pytest.raises(CapacityError, match='condition'):
        interpolate_hermite([HermiteDatum(Fraction(1), (1, 1))], degree_bound=0,
                            limits=HermiteLimits(max_conditions=1))
    with pytest.raises(CapacityError, match='operation'):
        interpolate_hermite([HermiteDatum(Fraction(1), (1,))], degree_bound=0,
                            limits=HermiteLimits(max_operations=1))
    with pytest.raises(ValueError, match='insufficient'):
        count_from_manual_designs(formula, [(1, design)], huge, order=0)
    incomplete = replace(design, matrices=((), ()))
    with pytest.raises(ValueError, match='outside measurement row space'):
        count_from_manual_designs(formula, [(1, incomplete), (2, incomplete)], order=1)


def test_nontrivial_rank_deficient_cross_group_measurement_certificates() -> None:
    """At t=1, cross-group dependencies use single shared measurements."""
    formula = CNFFormula(4, ((1, -3), (2, 4)))
    groups = ((0, 1), (2, 3))
    restricted_design = MeasurementDesign(
        groups, (0, 1), (((1, 1),), ((1, -1),)), Fraction(1, 2), 2)
    base = ReplacementSystem.identity(formula)
    rows = []
    for e, forms in enumerate(base.clauses):
        new_forms = []
        for j, form in enumerate(forms):
            outside = 1 - e
            target = (Fraction(2), Fraction(2)) if outside == 0 else (Fraction(3), Fraction(-3))
            coeffs = list(form.coefficients)
            for k, index in enumerate(groups[outside]):
                # At T=1, the outside vector is proportional to one measurement row.
                coeffs[index] = coeffs[index] + Polynomial((0, target[k] - coeffs[index].at_zero))
            # Local dependence can have different rational Taylor behavior.
            local_index = groups[e][j]
            coeffs[local_index] += Polynomial((0, Fraction(-j - 1, 5), Fraction(1, 11)))
            new_forms.append(ReplacementForm(tuple(coeffs)))
        rows.append(tuple(new_forms))
    system = ReplacementSystem(tuple(rows))
    direct = deformation_polynomial(formula, system)
    result = taylor_coefficients_separated(formula, restricted_design, system,
                                           at=1, order=2)
    target = direct.taylor(1, 2).coefficients
    assert result.coefficients == target + (0,) * (3 - len(target))
    assert result.certificate.total_measurements == 2
    assert any(any(weight != 0 for weight in lambdas)
               for forms in result.certificate.occurrences
               for occurrence in forms
               for lambdas in occurrence.lambda_by_group)
    with pytest.raises(ValueError, match='outside measurement row space'):
        taylor_coefficients_separated(formula, restricted_design, system,
                                      at=2, order=1)


def test_occurrence_and_replacement_preflight_budget() -> None:
    formula = CNFFormula(3, ((1, 2, 3),))
    design = coordinate_design(formula)
    with pytest.raises(CapacityError, match='occurrence'):
        taylor_coefficients_separated(formula, design, at=1, order=0,
                                      limits=TaylorLimits(max_occurrences=2))
    base = ReplacementSystem.identity(formula)
    p = Polynomial((1,) + (0,) * 16 + (1,))
    modified = ReplacementSystem(((ReplacementForm((p, ZERO, ZERO)),
                                   *base.clauses[0][1:]),))
    with pytest.raises(CapacityError, match='degree'):
        taylor_coefficients_separated(formula, design, modified, at=1, order=1,
                                      limits=TaylorLimits(max_replacement_degree=16))
    with pytest.raises(CapacityError, match='center bit'):
        taylor_coefficients_separated(formula, design, at=1 << 100, order=0,
                                      limits=TaylorLimits(max_coefficient_bits=10))
