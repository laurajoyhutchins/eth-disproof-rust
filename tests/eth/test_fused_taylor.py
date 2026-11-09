"""Fused exact Taylor contraction against the original Boolean differences.

For |E|>q the full finite difference is divisible by z**|E|, hence
the truncated Taylor jet equals one factored Boolean deformation sum.
The optimized path is a *different evaluation* of the same construction.
Its factor scopes may be dense. It is not a worst-case ETH proof.
"""
from __future__ import annotations

from dataclasses import replace

import pytest

from non_exponential_sudoku.eth import CNFFormula, construct_bounded_designs, count_bruteforce
from non_exponential_sudoku.eth.pipeline import ReferencePipelineConfig, count_cnf_reference
from non_exponential_sudoku.eth.taylor import (
    TaylorLimits, taylor_coefficients_separated,
)
from non_exponential_sudoku.runtime.budget import CapacityError


@pytest.mark.integration
@pytest.mark.parametrize("formula", (
    CNFFormula(2, ((1, 2),)),
    CNFFormula(3, ((1, -2), (-1, 3))),
    CNFFormula(4, ((1, 2), (2, 3), (-3, 4))),
))
def test_fusing_boolean_differences_preserves_every_taylor_coefficient(
    formula: CNFFormula,
) -> None:
    constructed = construct_bounded_designs(
        formula, r=2, Q=2, R=2, measurement_basis="projector",
    )
    for center, design in constructed.centers:
        for order in (0, 1, 2):
            explicit = taylor_coefficients_separated(
                formula, design, constructed.replacements,
                at=center, order=order, summation="tuples",
            )
            fused = taylor_coefficients_separated(
                formula, design, constructed.replacements,
                at=center, order=order, summation="fused",
            )
            assert fused.coefficients == explicit.coefficients
            assert fused.stats.taylor_pairs == 0
            assert fused.stats.measurement_tuples == 0
            assert fused.stats.factor_scope_basis == "variables"
            assert fused.stats.factor_assignments_tested >= 0


@pytest.mark.integration
def test_fused_taylor_matches_independent_full_polynomial_oracle() -> None:
    # This independent oracle enumerates the Boolean cube to construct H(T)
    # symbolically. It is never imported by the production fused evaluator.
    from fractions import Fraction
    from non_exponential_sudoku.eth.polynomial import deformation_polynomial

    formula = CNFFormula(3, ((1, -2), (-1, 3)))
    constructed = construct_bounded_designs(
        formula, r=2, Q=2, R=2, measurement_basis="projector",
    )
    polynomial = deformation_polynomial(formula, constructed.replacements)
    assert polynomial.at_zero == count_bruteforce(formula)
    for center, design in constructed.centers:
        for order in (0, 1, 2, 3):
            expected = polynomial.taylor(center, order).coefficients
            padded = expected + (Fraction(0),) * (order + 1 - len(expected))
            actual = taylor_coefficients_separated(
                formula, design, constructed.replacements,
                at=center, order=order, summation="fused",
            )
            assert actual.coefficients == padded


@pytest.mark.integration
def test_full_pipeline_path_four_avoids_explicit_taylor_pairs() -> None:
    formula = CNFFormula(4, ((1, 2), (2, 3), (3, 4)))
    result = count_cnf_reference(
        formula, config=replace(ReferencePipelineConfig(), summation="fused"),
    )
    assert result.count == count_bruteforce(formula) == 8
    assert result.summation == "fused"
    assert all(leaf.taylor_pairs == 0 for leaf in result.leaves)
    assert any(leaf.factor_assignments_tested > 0 for leaf in result.leaves)
    assert all(leaf.factor_scope_basis == "variables"
               for leaf in result.leaves if leaf.method == "certified-construction")


@pytest.mark.integration
def test_fused_factor_bound_refuses_without_hidden_fallback() -> None:
    formula = CNFFormula(2, ((1, 2),))
    constructed = construct_bounded_designs(formula, r=2, Q=2, R=2)
    center, design = constructed.centers[0]
    with pytest.raises(CapacityError, match="factor"):
        taylor_coefficients_separated(
            formula, design, constructed.replacements,
            at=center, order=1, summation="fused",
            limits=TaylorLimits(max_factor_entries=1),
        )


@pytest.mark.checkpoint
def test_fused_strategy_is_validated() -> None:
    assert ReferencePipelineConfig(summation="fused").summation == "fused"
    with pytest.raises(ValueError, match="unknown exact Taylor"):
        ReferencePipelineConfig(summation="invented")  # type: ignore[arg-type]


@pytest.mark.integration
@pytest.mark.requires_flint
def test_fused_exact_native_arithmetic_matches_python_reference() -> None:
    pytest.importorskip("flint")
    formula = CNFFormula(3, ((1, -2), (-1, 3)))
    constructed = construct_bounded_designs(
        formula, r=2, Q=2, R=2, measurement_basis="projector",
    )
    for center, design in constructed.centers:
        python = taylor_coefficients_separated(
            formula, design, constructed.replacements,
            at=center, order=2, summation="fused", backend="python",
        )
        flint = taylor_coefficients_separated(
            formula, design, constructed.replacements,
            at=center, order=2, summation="fused", backend="flint",
        )
        assert flint.coefficients == python.coefficients
        assert flint.stats.factor_assignments_tested == python.stats.factor_assignments_tested
        assert flint.stats.factor_scope_peak == python.stats.factor_scope_peak
