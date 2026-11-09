"""Exact factorized Taylor sums against the original separated tuple oracle.

Every comparison retains certified center-specific measurement witnesses.
Factorization is a different *evaluation* of the same restricted sum, not
a relaxation of the measurement-separation contract.
"""
from __future__ import annotations

from fractions import Fraction
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, MeasurementDesign, Polynomial, ReplacementForm,
    ReplacementSystem, count_bruteforce,
)
from non_exponential_sudoku.eth.taylor import (
    TaylorLimits, restricted_taylor_sum, taylor_coefficients_separated,
)
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def paired_groups(formula: CNFFormula) -> MeasurementDesign:
    assert formula.nvars % 2 == 0
    groups = tuple((i, i + 1) for i in range(0, formula.nvars, 2))
    matrix = ((1, 0), (0, 1))
    # Every group measures its own two Boolean coordinates exactly.
    return MeasurementDesign(
        groups=groups, clause_groups=tuple(
            max(0, (abs(clause[0]) - 1) // 2) if clause else 0
            for clause in formula.clauses),
        matrices=tuple(matrix for _ in groups),
        tau=Fraction(1, 2), D=1,
    )


def deformed(formula: CNFFormula) -> ReplacementSystem:
    base = ReplacementSystem.identity(formula)
    return ReplacementSystem(tuple(tuple(
        ReplacementForm(tuple(
            poly + Polynomial((0, Fraction((e + 2) * (i % 3 - 1), 5)))
            for i, poly in enumerate(form.coefficients)))
        for form in forms)
        for e, forms in enumerate(base.clauses)))


@pytest.mark.parametrize('seed', range(5))
def test_factorized_jets_equal_tuple_oracle_and_independent_count(seed: int) -> None:
    rng = Random(7262 + seed)
    formula = CNFFormula(6, tuple(tuple(
        rng.choice((-1, 1)) * rng.randint(1, 6)
        for _ in range(rng.randint(0, 3)))
        for _ in range(rng.randint(0, 3))))
    design = paired_groups(formula)
    replacements = deformed(formula)
    for order, E, U in ((0, (), ()), (1, (0,), ()), (2, (0, 3), (3,))):
        for center in (Fraction(1), Fraction(-2, 3)):
            original = restricted_taylor_sum(
                formula, design, replacements, at=center,
                E=E, U=U, order=order, summation='tuples')
            factorized = restricted_taylor_sum(
                formula, design, replacements, at=center,
                E=E, U=U, order=order, summation='eliminate')
            assert factorized.coefficients == original.coefficients
            assert factorized.stats.measurement_tuples == 0
            assert factorized.stats.factor_scope_peak <= len(design.groups)
    assert taylor_coefficients_separated(
        formula, design, replacements, at=Fraction(1), order=0,
        summation='eliminate').coefficients[0] == count_bruteforce(formula)


def test_factorized_taylor_matches_original_multijet() -> None:
    formula = CNFFormula(4, ((1, -3), (2, 4), (-1, -2, 4)))
    design = paired_groups(formula)
    system = deformed(formula)
    for order in (0, 1, 2):
        original = taylor_coefficients_separated(
            formula, design, system, at=Fraction(3, 2), order=order)
        factorized = taylor_coefficients_separated(
            formula, design, system, at=Fraction(3, 2), order=order,
            summation='eliminate')
        assert factorized.coefficients == original.coefficients
        assert factorized.stats.factor_eliminations > 0


def test_twenty_variable_chain_avoids_3_power_20_measurement_tuples() -> None:
    # Ten path variables with independent free partners. Number of legal
    # path assignments is F_12=144, times 2**10 unconstrained partners.
    formula = CNFFormula(20, tuple((2 * i + 1, 2 * i + 3)
                                   for i in range(9)))
    design = paired_groups(formula)
    with pytest.raises(CapacityError, match='tuple'):
        taylor_coefficients_separated(
            formula, design, at=1, order=0, summation='tuples',
            limits=TaylorLimits(max_measurement_tuples=1000))
    result = taylor_coefficients_separated(
        formula, design, at=1, order=0, summation='eliminate',
        limits=TaylorLimits(max_measurement_tuples=1, max_factor_entries=128))
    assert result.coefficients == (Fraction(144 * (1 << 10)),)
    assert result.stats.measurement_tuples == 0
    assert result.stats.factor_scope_peak <= 2
    assert result.stats.factor_entries_peak <= 128
    assert result.stats.factor_eliminations == 10


def test_independent_groups_contribute_without_boolean_enumeration() -> None:
    formula = CNFFormula(30, ())
    design = paired_groups(formula)
    result = taylor_coefficients_separated(
        formula, design, at=1, order=0, summation='eliminate',
        limits=TaylorLimits(max_measurement_tuples=1, max_factor_entries=4))
    assert result.coefficients == (Fraction(1 << 30),)
    assert result.stats.factor_assignments_tested == 0


def test_factor_work_and_size_cap_fail_closed() -> None:
    formula = CNFFormula(8, ((1, 3), (3, 5), (5, 7)))
    design = paired_groups(formula)
    with pytest.raises(CapacityError, match='factor'):
        taylor_coefficients_separated(
            formula, design, at=1, order=0, summation='eliminate',
            limits=TaylorLimits(max_factor_entries=3))
    with pytest.raises(CapacityError, match='factor'):
        taylor_coefficients_separated(
            formula, design, at=1, order=0, summation='eliminate',
            limits=TaylorLimits(max_factor_work=1))
    with pytest.raises(ValueError, match='summation'):
        taylor_coefficients_separated(
            formula, design, at=1, order=0, summation='unknown')  # type: ignore[arg-type]
