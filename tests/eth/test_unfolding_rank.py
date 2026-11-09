"""Exact rational tensor unfolding ranks of bounded CNF deformations.

The ranks are mathematical certificates for *specified cuts*, not an
unconditional complexity lower bound. A disjoint crossing-pairs family has
exponential middle rank under a bad ordering but bond rank two when pairs
are interleaved. Both are verified against explicit truth tables.
"""
from __future__ import annotations

from fractions import Fraction

import pytest

from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
from non_exponential_sudoku.eth.construction import construct_bounded_designs
from non_exponential_sudoku.eth.polynomial import deformation_polynomial
from non_exponential_sudoku.eth.unfolding_rank import (
    RankLimits, crossing_pair_witness, minimax_unfolding_order, rank_profile, unfolding_rank,
)
from non_exponential_sudoku.runtime.budget import CapacityError


@pytest.mark.checkpoint
@pytest.mark.parametrize("pairs", (1, 2))
def test_crossing_rank_obstruction_is_exact_for_each_cut(pairs: int) -> None:
    formula, replacements = crossing_pair_witness(pairs)
    cut = tuple(range(pairs))
    at_zero = unfolding_rank(formula, replacements, at=0, left_variables=cut)
    at_one = unfolding_rank(formula, replacements, at=1, left_variables=cut)
    assert at_zero.rank == 1
    assert at_zero.total_value == 2 ** pairs
    assert at_one.rank == 2 ** pairs
    assert at_one.total_value == 4 ** pairs
    assert at_one.boundary_rank_upper == 2 ** pairs
    assert at_one.left_boundary_size == at_one.right_boundary_size == pairs
    assert at_one.rational_operations > 0


@pytest.mark.integration
@pytest.mark.parametrize("pairs", (3, 4, 5))
def test_crossing_rank_exponential_for_a_specified_bipartition(pairs: int) -> None:
    formula, replacements = crossing_pair_witness(pairs)
    center = Fraction(3, 2)
    cut = tuple(range(pairs))
    evidence = unfolding_rank(formula, replacements, at=center, left_variables=cut)
    assert evidence.rank == 2 ** pairs
    assert evidence.boundary_rank_upper == evidence.rank
    assert evidence.total_value == (2 + 2 * center) ** pairs
    assert evidence.matrix_cells == 4 ** pairs
    assert evidence.max_coefficient_bits >= 1


@pytest.mark.integration
@pytest.mark.parametrize("pairs", (2, 3, 4))
def test_crossing_witness_is_easy_after_interleaving(pairs: int) -> None:
    formula, replacements = crossing_pair_witness(pairs)
    grouped = tuple(range(2 * pairs))
    interleaved = tuple(index for i in range(pairs)
                        for index in (i, i + pairs))
    grouped_profile = rank_profile(formula, replacements, at=1, variable_order=grouped)
    interleaved_profile = rank_profile(
        formula, replacements, at=1, variable_order=interleaved,
    )
    assert max(item.rank for item in grouped_profile) == 2 ** pairs
    assert max(item.rank for item in interleaved_profile) == 2
    assert all(item.rank <= item.boundary_rank_upper
               for item in grouped_profile + interleaved_profile)


@pytest.mark.integration
def test_exhaustive_minimax_order_is_exactly_two_for_crossing_pairs() -> None:
    # Proves that the apparently exponential *grouped* rank in the same
    # 6-variable tensor is wholly avoidable by a variable permutation.
    formula, replacements = crossing_pair_witness(3)
    optimum = minimax_unfolding_order(formula, replacements, at=1)
    assert optimum.peak_rank == 2
    assert optimum.cuts_checked == (1 << formula.nvars) - 2
    assert max(optimum.cut_ranks) == 2
    assert tuple(sorted(optimum.variable_order)) == tuple(range(formula.nvars))
    assert optimum.charged_rational_operations > 0


@pytest.mark.integration
def test_minimax_order_is_no_worse_than_natural_path_order() -> None:
    path = CNFFormula(4, ((1, 2), (2, 3), (3, 4)))
    optimum = minimax_unfolding_order(path, at=0)
    natural = rank_profile(path, at=0, variable_order=(0, 1, 2, 3))
    assert optimum.peak_rank <= max(cut.rank for cut in natural)
    assert optimum.cuts_checked == 14


@pytest.mark.integration
def test_subset_minimax_agrees_with_independent_all_permutations_oracle() -> None:
    from itertools import permutations

    formula = CNFFormula(4, ((1, 2), (2, 3), (3, 4)))
    objective = min(
        max(cut.rank for cut in rank_profile(formula, at=0, variable_order=order))
        for order in permutations(range(formula.nvars))
    )
    optimum = minimax_unfolding_order(formula, at=0)
    assert optimum.peak_rank == objective


@pytest.mark.checkpoint
def test_minimax_exhaustive_cut_limit_refuses_before_enumeration() -> None:
    formula, replacement = crossing_pair_witness(3)
    with pytest.raises(CapacityError, match="cut search"):
        minimax_unfolding_order(formula, replacement, at=1, max_cuts=10)


@pytest.mark.integration
def test_path_has_small_exact_cut_rank_under_natural_order() -> None:
    n = 7
    path = CNFFormula(n, tuple((i, i + 1) for i in range(1, n)))
    profile = rank_profile(path, at=0, variable_order=tuple(range(n)))
    assert len(profile) == n - 1
    assert max(item.rank for item in profile) <= 2
    assert all(item.boundary_rank_upper <= 2 for item in profile)
    assert profile[-1].total_value == count_bruteforce(path)


@pytest.mark.integration
def test_actual_certified_construction_rank_and_sum_agree_with_h() -> None:
    formula = CNFFormula(3, ((1, 2), (2, 3)))
    construction = construct_bounded_designs(
        formula, r=2, Q=2, R=2, measurement_basis="projector",
    )
    h = deformation_polynomial(formula, construction.replacements)
    for center, _ in construction.centers:
        cut = unfolding_rank(
            formula, construction.replacements,
            at=center, left_variables=(0,),
        )
        assert cut.total_value == h.evaluate(center)
        assert 0 <= cut.rank <= cut.boundary_rank_upper <= 2
    origin = unfolding_rank(
        formula, construction.replacements, at=0, left_variables=(0,),
    )
    assert origin.total_value == count_bruteforce(formula)


@pytest.mark.checkpoint
def test_empty_and_false_formula_have_exact_zero_or_unit_rank() -> None:
    empty = unfolding_rank(CNFFormula(3, ()), at=0, left_variables=(0,))
    contradiction = unfolding_rank(CNFFormula(3, ((),)), at=0,
                                    left_variables=(0,))
    assert empty.rank == 1 and empty.total_value == 8
    assert contradiction.rank == 0 and contradiction.total_value == 0
    assert empty.boundary_rank_upper == contradiction.boundary_rank_upper == 1


@pytest.mark.checkpoint
def test_rank_oracle_rejects_implicit_exponential_work_and_invalid_inputs() -> None:
    formula, replacements = crossing_pair_witness(3)
    with pytest.raises(CapacityError, match="cells"):
        unfolding_rank(
            formula, replacements, at=1,
            left_variables=(0, 1, 2), limits=RankLimits(max_cells=32),
        )
    with pytest.raises(CapacityError, match="rational operations"):
        unfolding_rank(
            formula, replacements, at=1, left_variables=(0, 1, 2),
            limits=RankLimits(max_rational_operations=2),
        )
    with pytest.raises(ValueError, match="permutation"):
        rank_profile(formula, replacements, at=1, variable_order=(0, 0))
    with pytest.raises(ValueError, match="left_variables"):
        unfolding_rank(formula, replacements, at=1, left_variables=(0, 0))
    with pytest.raises(TypeError):
        unfolding_rank(formula, replacements, at=0.5, left_variables=(0,))


@pytest.mark.integration
def test_rank_experiment_is_source_stable_and_does_not_claim_a_solver_bound() -> None:
    from benchmarks.eth.unfolding_rank import experiment

    report = experiment(max_pairs=2)
    assert report["status"] == "complete"
    assert report["inputs_stable"] is True
    assert len(report["constructed_samples"]) >= 4
    assert {s["nvars"] for s in report["constructed_samples"]} == {3, 4}
    assert all(s["certified_best_order"]["max_rank"]
               <= s["rank_profile"]["max_rank"]
               for s in report["constructed_samples"])
    assert report["pair_witnesses"][-1]["grouped_at_one"]["max_rank"] == 4
    assert report["pair_witnesses"][-1]["interleaved_at_one"]["max_rank"] == 2
    assert report["pair_witnesses"][-1]["exhaustive_best_order"]["max_rank"] == 2
    assert report["interpretation"]["worst_case"].startswith("no non-exponential")
