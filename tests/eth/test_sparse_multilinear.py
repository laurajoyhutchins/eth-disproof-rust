"""Independent exact polynomial-support tests for dense Boolean interactions.

A degree-2 clause can have O(n²) multilinear monomials even when its
replacement support spans all n Boolean variables. Products of clauses can
still reach 2**n monomials, so the new representation must refuse honestly.
"""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction
from math import comb

import pytest

from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
from non_exponential_sudoku.eth.design import MeasurementDesign
from non_exponential_sudoku.eth.pipeline import ReferencePipelineConfig, count_cnf_reference
from non_exponential_sudoku.eth.polynomial import (
    Polynomial, ReplacementForm, ReplacementSystem, deformation_polynomial,
    ReferenceLimits,
)
from non_exponential_sudoku.eth.taylor import TaylorLimits, taylor_coefficients_separated
from non_exponential_sudoku.runtime.budget import CapacityError


def _single_group(formula: CNFFormula) -> MeasurementDesign:
    """Valid finite certificate, no cross-group measurements required."""
    return MeasurementDesign(
        groups=(tuple(range(formula.nvars)),),
        clause_groups=(0,) * len(formula.clauses),
        matrices=((),), tau=Fraction(0), D=0,
    )


def _dense_two_literal(n: int) -> tuple[CNFFormula, ReplacementSystem]:
    formula = CNFFormula(n, ((1, 2),))
    rows = []
    for literal_index, scalar in ((0, 1), (1, 2)):
        coefficients = tuple(Polynomial((
            Fraction(int(index == literal_index)), Fraction(scalar),
        )) for index in range(n))
        rows.append(ReplacementForm(coefficients))
    replacements = ReplacementSystem((tuple(rows),))
    replacements.validate(formula)
    return formula, replacements


@pytest.mark.integration
@pytest.mark.parametrize("n", (3, 5, 8))
@pytest.mark.parametrize("order", (0, 1, 2))
def test_sparse_monomials_match_independent_boolean_polynomial_oracle(
    n: int, order: int,
) -> None:
    formula, replacements = _dense_two_literal(n)
    center = Fraction(1, 2)
    polynomial = deformation_polynomial(formula, replacements)
    reference = polynomial.taylor(center, order)
    expected = reference.coefficients + (
        (Fraction(0),) * (order + 1 - len(reference.coefficients))
    )
    result = taylor_coefficients_separated(
        formula, _single_group(formula), replacements,
        at=center, order=order, summation="multilinear",
    )
    assert result.coefficients == expected
    assert result.stats.taylor_pairs == 0
    assert result.stats.measurement_tuples == 0
    assert result.stats.multilinear_term_products > 0
    assert result.stats.multilinear_support_peak <= 1 + n + comb(n, 2)
    assert result.stats.factor_scope_basis == "not_applicable"


@pytest.mark.integration
def test_dense_sixteen_variable_clause_does_not_enumerate_a_factor_table() -> None:
    n = 16
    formula, replacements = _dense_two_literal(n)
    result = taylor_coefficients_separated(
        formula, _single_group(formula), replacements,
        at=Fraction(0), order=2, summation="multilinear",
        limits=TaylorLimits(max_factor_entries=256, max_factor_work=50_000),
    )
    assert result.coefficients[0] == 3 * (1 << (n - 2))
    assert result.stats.multilinear_support_peak <= 1 + n + comb(n, 2)
    assert result.stats.multilinear_support_peak < 1 << n
    assert result.stats.factor_assignments_tested == 0
    # The *same* mathematically exact instance cannot fit as a 2**16
    # explicit Boolean-variable factor table under the identical cap.
    # This witnesses a genuine representational distinction, not a
    # claim about worst-case runtime or the source paper's schedule.
    with pytest.raises(CapacityError, match="factor entry limit"):
        taylor_coefficients_separated(
            formula, _single_group(formula), replacements,
            at=Fraction(0), order=2, summation="fused",
            limits=TaylorLimits(max_factor_entries=256, max_factor_work=50_000),
        )


@pytest.mark.integration
def test_exponential_monomial_growth_refuses_without_fallback() -> None:
    n = 8
    # Each negative unit clause is (not x_i): the joint polynomial is
    # product_i (1-x_i) and has exactly 2**n distinct Boolean monomials.
    formula = CNFFormula(n, tuple((-i,) for i in range(1, n + 1)))
    with pytest.raises(CapacityError, match="multilinear support"):
        taylor_coefficients_separated(
            formula, _single_group(formula),
            at=Fraction(1), order=0, summation="multilinear",
            limits=TaylorLimits(max_factor_entries=20),
        )


@pytest.mark.integration
def test_sparse_intermediate_live_tables_obey_shared_entry_budget() -> None:
    formula = CNFFormula(2, ((1, 2),))
    # The algorithm may have a small output but must not silently ignore
    # the intermediate-table retention cap, even for a tiny construction.
    with pytest.raises(CapacityError, match="multilinear total"):
        taylor_coefficients_separated(
            formula, _single_group(formula), at=Fraction(1), order=0,
            summation="multilinear",
            limits=TaylorLimits(max_factor_total_entries=2),
        )


@pytest.mark.integration
def test_full_cnf_pipeline_multilinear_path_four_is_exact() -> None:
    formula = CNFFormula(4, ((1, 2), (2, 3), (3, 4)))
    report = count_cnf_reference(
        formula, config=replace(ReferencePipelineConfig(), summation="multilinear"),
    )
    assert report.count == count_bruteforce(formula) == 8
    assert report.summation == "multilinear"
    assert any(leaf.multilinear_term_products > 0 for leaf in report.leaves)
    assert all(leaf.taylor_pairs == 0 for leaf in report.leaves)
    assert all(leaf.multilinear_support_peak <= (1 << leaf.prepared_variables)
               for leaf in report.leaves)
    assert all(leaf.factor_scope_basis == "not_applicable"
               for leaf in report.leaves if leaf.method == "certified-construction")


@pytest.mark.integration
@pytest.mark.requires_flint
def test_multilinear_native_flint_matches_python() -> None:
    pytest.importorskip("flint")
    formula, replacements = _dense_two_literal(5)
    args = dict(
        formula=formula, design=_single_group(formula), replacements=replacements,
        at=Fraction(2, 3), order=2, summation="multilinear",
    )
    ref = taylor_coefficients_separated(**args, backend="python")
    native = taylor_coefficients_separated(**args, backend="flint")
    assert native.coefficients == ref.coefficients
    assert native.stats.multilinear_term_products == ref.stats.multilinear_term_products
    assert native.stats.multilinear_support_peak == ref.stats.multilinear_support_peak


@pytest.mark.checkpoint
def test_multilinear_mode_is_opt_in() -> None:
    assert ReferencePipelineConfig().summation == "tuples"
    assert ReferencePipelineConfig(summation="multilinear").summation == "multilinear"
    with pytest.raises(ValueError, match="unknown exact Taylor"):
        ReferencePipelineConfig(summation="bogus")  # type: ignore[arg-type]
