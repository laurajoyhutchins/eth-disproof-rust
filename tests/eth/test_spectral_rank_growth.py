"""Actual spectral replacement support-rank growth: research acceptance tests."""
from __future__ import annotations

import pytest

from benchmarks.eth.spectral_rank_growth import experiment


@pytest.mark.integration
def test_actual_constructed_families_have_sound_upper_and_exact_evidence() -> None:
    report = experiment(
        families=("path", "matching", "clique"),
        sizes=(3, 4),
        max_exact_n=4,
    )
    assert report["status"] == "complete"
    assert report["inputs_stable"] is True
    cases = report["samples"]
    assert len(cases) == 5  # path 3/4, matching 4, clique 3/4
    assert all(case["status"] in ("verified", "construction_refusal") for case in cases)
    successful = [case for case in cases if case["status"] == "verified"]
    assert successful
    for case in successful:
        assert case["uniform"]["best_rank_upper"] >= 1
        assert case["finite_construction_status"].startswith("bounded-constructive-reference")
        assert type(case["lemma_hypotheses_met"]) is bool
        assert len(case["centers"]) == 2
        for center in case["centers"]:
            assert center["exact_best_rank"] <= case["uniform"]["best_rank_upper"]
            assert center["exact_rank_charged_rational_operations"] > 0
            assert center["exact_rank_max_coefficient_bits"] >= 1
            assert center["support_order_rank_peak"] <= case["uniform"]["best_rank_upper"]
            assert center["support_order_charged_rational_operations"] > 0
            assert center["independent_deformation_check"] is True
    assert report["mathematical_claims"]["worst_case_nonexponential"] is False
    assert report["mathematical_claims"]["uniform_rank_proved"] is False


@pytest.mark.checkpoint
def test_bounded_growth_rejects_invalid_ranges_and_empty_families() -> None:
    for opts in (
        {"families":(), "sizes":(3,)},
        {"families":("invented",), "sizes":(3,)},
        {"families":("path",), "sizes":(1,)},
        {"families":("path",), "sizes":(13,)},
        {"families":("path",), "sizes":(3,), "max_exact_n":13},
    ):
        with pytest.raises(ValueError):
            experiment(**opts)


@pytest.mark.integration
def test_actual_spectral_support_bound_is_valid_outside_sampled_centers() -> None:
    # This test is about symbolic polynomial support, not an empirical
    # regression of rank on two conveniently selected T values.
    from benchmarks.eth.cnf_scaling import scenario
    from non_exponential_sudoku.eth.construction import construct_bounded_designs
    from non_exponential_sudoku.eth.support_rank import minimax_uniform_support_order
    from non_exponential_sudoku.eth.unfolding_rank import rank_profile

    formula = scenario("path", 4).formula
    constructed = construct_bounded_designs(
        formula, r=2, Q=2, R=2, measurement_basis="projector",
    )
    bound = minimax_uniform_support_order(formula, constructed.replacements)
    for center in (-3, 0, 1, 2, 5):
        rank = rank_profile(
            formula, constructed.replacements, at=center,
            variable_order=bound.variable_order,
        )
        assert max(value.rank for value in rank) <= bound.peak_rank_upper
