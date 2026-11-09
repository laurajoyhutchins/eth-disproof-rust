"""Uniform-in-T support rank bounds for certified spectral CNF replacements.

Support-only certificates must be sound for the full polynomial and for
Taylor coefficients. Unlike exact rank, they do not inspect truth tables.
"""
from __future__ import annotations

from fractions import Fraction

import pytest

from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.construction import construct_bounded_designs
from non_exponential_sudoku.eth.polynomial import ReplacementSystem
from non_exponential_sudoku.eth.support_rank import (
    SupportRankLimits, minimax_uniform_support_order,
    polynomial_cut_bound, polynomial_clause_supports, uniform_support_profile,
)
from non_exponential_sudoku.eth.unfolding_rank import (
    RankLimits, crossing_pair_witness, minimax_unfolding_order,
    rank_profile, unfolding_rank,
)
from non_exponential_sudoku.runtime.budget import CapacityError


@pytest.mark.checkpoint
@pytest.mark.parametrize("pairs", (1, 2))
def test_uniform_polynomial_support_exposes_bad_order_and_best_order(pairs: int) -> None:
    formula, replacement = crossing_pair_witness(pairs)
    supports = polynomial_clause_supports(formula, replacement)
    grouped = tuple(range(pairs))
    middle = polynomial_cut_bound(supports, formula.nvars, grouped)
    optimum = minimax_uniform_support_order(formula, replacement)
    assert middle.rank_upper == 2 ** pairs
    assert middle.boundary_left == middle.boundary_right == pairs
    assert optimum.peak_rank_upper == 2
    assert optimum.upper_rank_per_cut
    assert optimum.cuts_examined == (1 << formula.nvars) - 2
    assert optimum.polynomial_terms_inspected >= 2 * pairs
    assert all(bound <= 2 for bound in optimum.upper_rank_per_cut)


@pytest.mark.integration
@pytest.mark.parametrize("pairs", (3, 4))
def test_uniform_bound_does_not_require_boolean_cube_oracle(pairs: int) -> None:
    formula, replacements = crossing_pair_witness(pairs)
    optimum = minimax_uniform_support_order(
        formula, replacements, limits=SupportRankLimits(max_variables=12),
    )
    grouped = polynomial_cut_bound(
        polynomial_clause_supports(formula, replacements),
        formula.nvars, tuple(range(pairs)),
    )
    assert optimum.peak_rank_upper == 2
    assert grouped.rank_upper == (1 << pairs)


@pytest.mark.integration
@pytest.mark.parametrize("family", ("path", "matching", "xor_pairs", "clique"))
def test_uniform_bound_is_sound_for_real_spectral_construction(family: str) -> None:
    from benchmarks.eth.cnf_scaling import scenario

    n = 4
    formula = scenario(family, n).formula
    construction = construct_bounded_designs(
        formula, r=2, Q=2, R=2, measurement_basis="projector",
    )
    certificate = minimax_uniform_support_order(formula, construction.replacements)
    assert certificate.peak_rank_upper >= 1
    assert certificate.polynomial_terms_inspected > 0
    assert certificate.cuts_examined == 14

    for center, _design in construction.centers:
        optimum = minimax_unfolding_order(
            formula, construction.replacements, at=center,
        )
        assert optimum.peak_rank <= certificate.peak_rank_upper
        order_ranks = rank_profile(
            formula, construction.replacements, at=center,
            variable_order=certificate.variable_order,
        )
        assert max(x.rank for x in order_ranks) <= certificate.peak_rank_upper
        for idx, actual in enumerate(order_ranks):
            cut = polynomial_cut_bound(
                polynomial_clause_supports(formula, construction.replacements),
                formula.nvars, certificate.variable_order[:idx + 1],
            )
            assert actual.rank <= cut.rank_upper


@pytest.mark.integration
def test_polynomial_bound_is_sound_at_origin_and_outside_certified_centers() -> None:
    formula, replacement = crossing_pair_witness(2)
    certificate = minimax_uniform_support_order(formula, replacement)
    assert certificate.peak_rank_upper == 2
    for center in (Fraction(-7, 3), Fraction(0), Fraction(1), Fraction(3, 2)):
        profile = rank_profile(
            formula, replacement, at=center,
            variable_order=certificate.variable_order,
        )
        assert max(x.rank for x in profile) <= certificate.peak_rank_upper


@pytest.mark.integration
def test_symbolic_support_bounds_each_taylor_coefficient_rank() -> None:
    # Coefficient [z^j] of f(T+z) is a sum of j+1 products of
    # separated functions, so rank_Q(coefficient_j) <= (j+1)*U.
    from non_exponential_sudoku.eth.polynomial import clause_satisfaction_polynomial
    from non_exponential_sudoku.eth.support_rank import coefficient_unfolding_rank

    formula, replacement = crossing_pair_witness(2)
    certificate = minimax_uniform_support_order(formula, replacement)
    for order in (0, 1, 2):
        coeff = coefficient_unfolding_rank(
            formula, replacement, center=Fraction(1, 2),
            order=order, left_variables=(0, 2),
        )
        cut = polynomial_cut_bound(
            polynomial_clause_supports(formula, replacement),
            formula.nvars, (0, 2),
        )
        assert coeff.rank <= (order + 1) * cut.rank_upper
        assert coeff.rank <= min(coeff.matrix_rows, coeff.matrix_columns)


@pytest.mark.checkpoint
def test_uniform_support_budget_refuses_without_fallback() -> None:
    formula, replacement = crossing_pair_witness(3)
    with pytest.raises(CapacityError, match="subset"):
        minimax_uniform_support_order(
            formula, replacement, limits=SupportRankLimits(max_subsets=15),
        )
    with pytest.raises(CapacityError, match="support"):
        minimax_uniform_support_order(
            formula, replacement, limits=SupportRankLimits(max_support_checks=1),
        )
    with pytest.raises(ValueError):
        polynomial_cut_bound(((1 << 5,),), 3, (0,))
    with pytest.raises(ValueError):
        polynomial_cut_bound((3,), 3, (0, 0))


@pytest.mark.checkpoint
def test_identity_path_has_uniform_rank_two_in_natural_order() -> None:
    n = 6
    formula = CNFFormula(n, tuple((i, i + 1) for i in range(1, n)))
    supports = polynomial_clause_supports(
        formula, ReplacementSystem.identity(formula),
    )
    assert all(
        polynomial_cut_bound(supports, n, tuple(range(i))).rank_upper <= 2
        for i in range(1, n)
    )
    assert minimax_uniform_support_order(formula).peak_rank_upper == 2


@pytest.mark.checkpoint
def test_large_identity_path_has_linear_cost_support_certificate() -> None:
    # This is a symbolic factor-support fact, not a Boolean cube oracle.
    n = 64
    formula = CNFFormula(n, tuple((i, i + 1) for i in range(1, n)))
    rank_profile = uniform_support_profile(formula, variable_order=tuple(range(n)))
    assert len(rank_profile) == n - 1
    assert max(cut.rank_upper for cut in rank_profile) == 2
    assert sum(cut.crossing_factors for cut in rank_profile) == n - 1
    with pytest.raises(ValueError, match="permutation"):
        uniform_support_profile(formula, variable_order=(0, 0))
