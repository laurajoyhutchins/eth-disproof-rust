"""Contracts for source-pinned growing CNF experiments, not a complexity proof."""
from __future__ import annotations

from dataclasses import replace
import json
from subprocess import TimeoutExpired

import pytest

from non_exponential_sudoku.eth.cnf import count_bruteforce
from benchmarks.eth.cnf_scaling import (
    FAMILIES, MODES, SUMMATIONS, _run_worker, run, sample_once,
    scenario, summarize,
)


@pytest.mark.checkpoint
@pytest.mark.parametrize("family", FAMILIES)
@pytest.mark.parametrize("n", (2, 4, 6, 8))
def test_family_oracles_are_independent_of_constructed_count(family: str, n: int) -> None:
    fixture = scenario(family, n)
    assert fixture.expected_count == count_bruteforce(fixture.formula)
    assert fixture.formula.nvars == n


@pytest.mark.checkpoint
def test_input_validation_rejects_odd_pairs_and_unbounded_sizes() -> None:
    for family, n in (("matching", 3), ("xor_pairs", 5), ("path", 1),
                      ("path", 65), ("not-a-family", 4)):
        with pytest.raises(ValueError):
            scenario(family, n)


def _row(mode: str, status: str = "verified",
         actual: int | None = 3) -> dict[str, object]:
    return {
        "family": "path", "nvars": 2, "summation": "eliminate",
        "mode": mode, "status": status, "expected_count": 3,
        "exact_count": actual if status == "verified" else None,
        "elapsed_ns": 1000 if status in ("verified", "capacity_refusal") else None,
        "peak_process_rss_bytes": 4096 if status in ("verified", "capacity_refusal") else None,
        "peak_python_traced_bytes": 512 if mode == "observed" else None,
    }


@pytest.mark.checkpoint
def test_reconciled_exact_and_refusal_outcomes_are_distinct() -> None:
    verified = summarize([_row("baseline"), _row("observed")], 1)
    assert verified["outcome"] == "verified"
    assert verified["answer_verified"] is True
    assert verified["instrumentation_walltime_ratio"] == 1.0

    refused = summarize([
        _row("baseline", "capacity_refusal"),
        _row("observed", "capacity_refusal"),
    ], 1)
    assert refused["outcome"] == "capacity_refusal"
    assert refused["answer_verified"] is False
    assert refused["instrumentation_walltime_ratio"] is None

    timed_out = summarize([_row("baseline", "timeout"), _row("observed", "timeout")], 1)
    assert timed_out["outcome"] == "timeout"
    assert timed_out["answer_verified"] is False


@pytest.mark.checkpoint
def test_mismatched_or_incomplete_evidence_fails_closed() -> None:
    for rows in (
        [_row("baseline")],
        [_row("baseline"), _row("baseline")],
        [_row("baseline"), _row("observed", actual=2)],
        [_row("baseline"), {**_row("observed"), "status": "failed"}],
    ):
        with pytest.raises(ValueError):
            summarize(rows, 1)


@pytest.mark.checkpoint
def test_instrumentation_sensitive_completion_is_preserved_not_compared() -> None:
    rows = [_row("baseline"), _row("observed", "timeout")]
    outcome = summarize(rows, 1)
    assert outcome["outcome"] == "discordant_outcomes"
    assert outcome["arm_outcomes"] == {
        "baseline": "verified", "observed": "timeout",
    }
    assert outcome["answer_verified"] is False
    assert outcome["instrumentation_walltime_ratio"] is None
    # Disagreement is real evidence, not an excuse to erase the completed arm.
    assert rows[0]["exact_count"] == 3
    assert rows[1]["exact_count"] is None
    with pytest.raises(ValueError):
        summarize([
            _row("baseline", actual=2), _row("observed", "timeout"),
        ], 1)


@pytest.mark.checkpoint
def test_worker_timeout_keeps_null_exact_count(monkeypatch: pytest.MonkeyPatch) -> None:
    import benchmarks.eth.cnf_scaling as m

    def time_out(*args: object, **kwargs: object) -> None:
        raise TimeoutExpired("python", 0.01)

    monkeypatch.setattr(m.subprocess, "run", time_out)
    result = _run_worker(
        "path", 4, "tuples", "baseline",
        timeout=0.01, threshold=64, max_leaves=64, r=2, Q=2, R=2,
        backend="python", oracle_max_vars=12,
    )
    assert result["status"] == "timeout"
    assert result["exact_count"] is None


@pytest.mark.checkpoint
def test_report_never_claims_an_asymptotic_bound(monkeypatch: pytest.MonkeyPatch) -> None:
    import benchmarks.eth.cnf_scaling as m

    def worker(family: str, n: int, summation: str, mode: str, **kwargs: object):
        return _row(mode, "capacity_refusal")

    monkeypatch.setattr(m, "_run_worker", worker)
    report = run(
        ["path"], [2], ["eliminate"], repeats=1, timeout=1,
        threshold=64, max_leaves=64, r=2, Q=2, R=2,
        backend="python", oracle_max_vars=12,
    )
    assert report["status"] == "complete"
    assert report["all_cases_solved"] is False
    assert report["outcome_counts"] == {"capacity_refusal": 1}
    assert report["analytical"]["complete_worst_case_bit_bound"] is None


@pytest.mark.integration
def test_real_complete_two_variable_cnf_is_exact_with_both_summations() -> None:
    for summation in SUMMATIONS:
        evidence = sample_once(
            "path", 2, summation, "baseline", threshold=64,
            max_leaves=64, r=2, Q=2, R=2,
            backend="python", oracle_max_vars=12,
        )
        assert evidence["status"] == "verified"
        assert evidence["exact_count"] == 3
        assert evidence["expected_count"] == 3
        assert evidence["leaf_evidence"]["leaves_completed"] >= 1
        assert evidence["leaf_evidence"]["max_coefficient_bits"] >= 0


@pytest.mark.integration
def test_full_worker_pair_is_source_stable_and_exact(tmp_path) -> None:
    report = run(
        ["matching"], [2], ["eliminate"], repeats=1, timeout=30,
        threshold=64, max_leaves=64, r=2, Q=2, R=2,
        backend="python", oracle_max_vars=12,
    )
    assert report["status"] == "complete"
    assert report["all_cases_solved"] is True
    assert report["measurements"][0]["summary"]["outcome"] == "verified"
    assert all(sample["exact_count"] == 3
               for sample in report["measurements"][0]["raw_samples"])
