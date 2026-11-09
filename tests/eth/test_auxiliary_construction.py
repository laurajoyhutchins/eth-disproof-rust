"""Exact spectral construction and bounded, transferred center certificates."""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, ConstructionLimits, construct_auxiliary,
    construct_bounded_designs, construct_from_schedules,
    count_bruteforce, count_from_constructed, deformation_polynomial,
    deterministic_schedules, certify_measurements,
)
from non_exponential_sudoku.eth.design import _row_combination
from non_exponential_sudoku.eth.evaluation import evaluate_separated
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def test_exact_auxiliary_spectral_contract() -> None:
    for r, Q, R, rows in ((2, 1, 1, 1), (2, 2, 2, 1), (2, 3, 2, 10),
                          (2, 2, 3, 0)):
        auxiliary = construct_auxiliary(r=r, Q=Q, R=R)
        assert auxiliary.dimension == r ** (2 * Q)
        assert len(auxiliary.measurements) == rows
        assert auxiliary.max_polynomial_degree <= R - 1
        for u, label in enumerate(auxiliary.labels):
            for w, poly in enumerate(auxiliary.rows[u]):
                assert poly.at_zero == int(u == w)
            for s in range(Q):
                others = tuple(w for w, target in enumerate(auxiliary.labels)
                               if target[s][0] != label[s][1])
                rows_outside = tuple(tuple(C[w] for w in others)
                                     for C in auxiliary.measurements)
                vector = tuple(auxiliary.rows[u][w].evaluate(s + 1) for w in others)
                lambdas = _row_combination(rows_outside, vector)
                assert all(sum((lambdas[j] * rows_outside[j][i]
                                for j in range(len(lambdas))), Fraction(0)) == vector[i]
                           for i in range(len(others)))


def test_transferred_designs_have_nonconstant_polynomials_and_exact_counts() -> None:
    fixtures = (
        CNFFormula(3, ((1, 2),)),
        CNFFormula(3, ((1, 2), (-1, 2))),
        CNFFormula(3, ((1, -2), (-1, 3), (2, 3))),
        CNFFormula(3, ()),
        CNFFormula(3, ((),)),
    )
    first = construct_bounded_designs(fixtures[0], r=2, Q=2, R=2, schedule='digits')
    assert first.auxiliary.max_polynomial_degree == 1
    assert any(p.degree == 1 for rows in first.replacements.clauses
               for form in rows for p in form.coefficients)
    for formula in fixtures:
        construction = construct_bounded_designs(formula, r=2, Q=2, R=2)
        assert construction.algorithm_status.startswith('bounded-constructive')
        assert construction.balancing is not None
        assert construction.balancing.final_potential <= construction.balancing.initial_potential
        assert len(construction.centers) == 2
        for center, design in construction.centers:
            cert = certify_measurements(formula, construction.replacements, design, at=center)
            assert cert.total_measurements == construction.max_measurement_rows
        assert count_from_constructed(formula, construction) == count_bruteforce(formula)
        if formula.nvars == 3 and len(formula.clauses) > 0:
            direct = deformation_polynomial(formula, construction.replacements)
            for center, design in construction.centers:
                assert evaluate_separated(formula, design, construction.replacements,
                                          at=center).value == direct.evaluate(center)


def test_randomized_exact_count_and_no_oracle_fallback(monkeypatch: pytest.MonkeyPatch) -> None:
    rng = Random(20261025)
    for _ in range(12):
        n = rng.choice((2, 3))
        raw = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                          for _ in range(rng.randint(0, 2)))
                    for _ in range(rng.randint(0, 2)))
        formula = CNFFormula(n, raw)
        expected = count_bruteforce(formula)
        construction = construct_bounded_designs(formula, r=2, Q=2, R=2)
        # A constructed count must not invoke any exhaustive #SAT reference.
        import non_exponential_sudoku.eth.cnf as cnf
        with monkeypatch.context() as p:
            p.setattr(cnf, 'count_bruteforce', lambda *args, **kwargs: (_ for _ in ()).throw(AssertionError('fallback')))
            assert count_from_constructed(formula, construction) == expected


def test_invalid_schedules_and_capacity_fail_closed() -> None:
    formula = CNFFormula(3, ((1, -2), (2, 3)))
    aux = construct_auxiliary(r=2, Q=2, R=2)
    a, d = deterministic_schedules(formula, r=2, Q=2)
    with pytest.raises(ValueError, match='schedule count'):
        construct_from_schedules(formula, aux, a[:-1], d)
    with pytest.raises(ValueError, match='schedules must contain'):
        construct_from_schedules(formula, aux, ((2, 0), *a[1:]), d)
    with pytest.raises(ValueError, match='small-group'):
        larger = construct_auxiliary(r=3, Q=1, R=1)
        construct_from_schedules(formula, larger, ((0,), (0,), (0,)), ((0,), (0,)))
    with pytest.raises(CapacityError, match='dimension'):
        construct_auxiliary(r=2, Q=3, R=2, limits=ConstructionLimits(max_dimension=16))
    with pytest.raises(CapacityError, match='occurrence'):
        construct_from_schedules(formula, aux, a, d,
                                 limits=ConstructionLimits(max_occurrences=1))
    with pytest.raises(CapacityError, match='measurement row'):
        construct_from_schedules(formula, aux, a, d,
                                 limits=ConstructionLimits(max_measurement_rows=1))
    with pytest.raises(ValueError, match='r>=2'):
        construct_auxiliary(r=1, Q=2, R=2)
    with pytest.raises(ValueError, match='nvars'):
        deterministic_schedules(CNFFormula(1, ((1,),)), r=2, Q=2)


def test_centers_are_independently_verified_and_flint_equal() -> None:
    formula = CNFFormula(3, ((1, -2), (2, 3)))
    construction = construct_bounded_designs(formula, r=2, Q=2, R=2)
    for center, design in construction.centers:
        altered = replace(design, matrices=tuple(() for _ in design.matrices),
                          tau=Fraction(0))
        with pytest.raises(ValueError, match='outside measurement row space'):
            certify_measurements(formula, construction.replacements, altered, at=center)
    pytest.importorskip('flint')
    assert count_from_constructed(formula, construction, backend='flint') == count_from_constructed(
        formula, construction, backend='python')
