"""Fail-closed full-input scaling contracts for distinct counting algorithms."""
from __future__ import annotations

import pytest

from benchmarks.sudoku_scaling import (DEFAULT_CASES, fixtures, sample,
                                        summarize, run)


def record(mode: str, status: str = "verified", count: int | None = 2) -> dict[str, object]:
    return {
        "case": "4x4-12-givens-two-solutions", "algorithm": "frontier",
        "mode": mode, "status": status, "expected_count": 2,
        "exact_count": count, "elapsed_ns": 100,
    }


@pytest.mark.checkpoint
def test_fixtures_preserve_complete_original_sudoku_inputs() -> None:
    all_cases = fixtures()
    assert len(DEFAULT_CASES) == len(set(DEFAULT_CASES))
    assert all_cases["4x4-empty"][1] == 288
    assert all_cases["9x9-hard-unique"][0].side == 9
    for puzzle, _ in all_cases.values():
        assert puzzle.b in (2, 3, 4)
        assert len(puzzle.entries) == puzzle.side * puzzle.side
        assert all(0 <= v <= puzzle.side for v in puzzle.entries)
    eight, oracle_expected = all_cases["16x16-248-givens-eight-holes"]
    assert sum(v == 0 for v in eight.entries) == 8
    assert oracle_expected is None


@pytest.mark.checkpoint
def test_verified_paired_scaling_data_is_not_a_complexity_claim() -> None:
    result = summarize([record("baseline"), record("observed")], 1)
    assert result["answer_verified"] is True
    assert result["outcome"] == "verified"
    assert result["instrumentation_walltime_ratio"] == 1.0


@pytest.mark.checkpoint
def test_explicit_capacity_refusal_is_not_reported_as_a_solution() -> None:
    result = summarize([record("baseline", "capacity_refusal", None),
                        record("observed", "capacity_refusal", None)], 1)
    assert result["outcome"] == "capacity_refusal"
    assert result["answer_verified"] is False
    assert result["instrumentation_walltime_ratio"] is None


@pytest.mark.checkpoint
def test_timeout_and_reference_refusal_are_not_verified() -> None:
    for status in ("timeout", "oracle_refusal"):
        result = summarize([record("baseline", status, None),
                            record("observed", status, None)], 1)
        assert result["answer_verified"] is False


@pytest.mark.checkpoint
def test_mismatched_or_failed_arms_are_not_accepted() -> None:
    with pytest.raises(ValueError):
        summarize([record("baseline"), record("baseline")], 1)
    with pytest.raises(ValueError):
        summarize([record("baseline"), record("observed", "capacity_refusal", None)], 1)
    with pytest.raises(ValueError):
        summarize([record("baseline"), record("observed", "failed", None)], 1)
    with pytest.raises(ValueError):
        summarize([record("baseline"), {**record("observed"), "exact_count": 3}], 1)


@pytest.mark.integration
def test_real_empty_four_by_four_frontier_count_and_observer() -> None:
    for mode in ("baseline", "observed"):
        row = sample("4x4-empty", "frontier", mode, 200_000)
        assert row["status"] == "verified"
        assert row["exact_count"] == row["expected_count"] == 288
        assert row["algorithm_stats"]["transitions"] > 0
        assert row["cells"] == 16
        assert row["blank_cells"] == 16


@pytest.mark.integration
def test_bounded_full_input_worker_pair() -> None:
    report = run(["4x4-12-givens-two-solutions"], ["frontier"],
                 1, 30, 200_000)
    assert report["status"] == "complete"
    assert report["all_cases_solved"] is True
    assert report["outcome_counts"]["verified"] == 1
    assert report["analytical"]["worst_case_bit_bound"] is None


@pytest.mark.integration
def test_paper_schedule_refusal_or_completion_is_explicit() -> None:
    row = sample("4x4-empty", "paper", "observed", 200_000)
    assert row["status"] in ("verified", "capacity_refusal")
    assert row["expected_count"] == 288
    if row["status"] == "verified":
        assert row["exact_count"] == 288
    else:
        assert row["exact_count"] is None
        assert row["refusal_reason"]
