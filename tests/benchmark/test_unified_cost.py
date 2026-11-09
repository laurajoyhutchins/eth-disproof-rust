"""Cost experiment contracts; no complexity claim from finite samples."""
from __future__ import annotations

import pytest

from benchmarks.unified_cost import CASES, UNKNOWN_COSTS, aggregate, run, sample_once


def record(mode: str, *, duration: int = 100) -> dict[str, object]:
    return {
        "status": "verified", "case": "parity-2wire",
        "variant": "reference", "mode": mode, "exact_count": 2,
        "expected": 2, "duration_ns": duration,
        "peak_process_rss_bytes": 123456,
        "tracemalloc_peak_bytes": 800 if mode == "observed" else None,
    }


@pytest.mark.checkpoint
def test_pairstats_preserve_raw_samples_and_expose_observer_cost() -> None:
    rows = [record("baseline", duration=100), record("observed", duration=150),
            record("observed", duration=180), record("baseline", duration=120)]
    summary = aggregate(rows, 2)
    assert summary["baseline"]["duration_ns"] == [100, 120]
    assert summary["observed"]["duration_ns"] == [150, 180]
    assert summary["instrumentation_walltime_ratio"] == 1.5


@pytest.mark.checkpoint
@pytest.mark.parametrize("bad", [
    {"status": "capacity_refused"},
    {"status": "failed"},
    {"status": "timeout"},
    {"status": "invalid"},
])
def test_fail_closed_on_any_incomplete_arm(bad: dict[str, str]) -> None:
    with pytest.raises(ValueError):
        aggregate([record("baseline"), {**record("observed"), **bad}], 1)


@pytest.mark.checkpoint
def test_reject_missing_duplicated_and_mismatched_pairs() -> None:
    with pytest.raises(ValueError):
        aggregate([record("baseline")], 1)
    with pytest.raises(ValueError):
        aggregate([record("baseline"), record("baseline")], 1)
    with pytest.raises(ValueError):
        aggregate([record("baseline"), {**record("observed"), "exact_count": 3}], 1)


@pytest.mark.checkpoint
def test_unknown_native_and_worst_case_costs_are_explicit() -> None:
    assert CASES
    assert any("bit" in gap for gap in UNKNOWN_COSTS)
    assert any("native" in gap for gap in UNKNOWN_COSTS)


@pytest.mark.integration
def test_traced_and_untraced_exact_results_match_with_reconciled_frames() -> None:
    base = sample_once("parity-2wire", "reference", "baseline")
    observed = sample_once("parity-2wire", "reference", "observed")
    assert base["exact_count"] == observed["exact_count"] == 2
    assert base["cost_ledger"] is None
    assert observed["cost_ledger"]["frame_tree_reconciled"]
    assert observed["cost_ledger"]["frames_observed"] >= 1
    assert observed["tracemalloc_peak_bytes"] >= 0
    assert observed["work_trace"]["scope"].startswith("optional")


@pytest.mark.integration
def test_end_to_end_isolated_workers_and_provenance() -> None:
    report = run(["parity-2wire"], ["reference"], 1, 60)
    assert report["status"] == "complete"
    assert len(report["measured"]) == 1
    assert report["measured"][0]["summary"]["repetitions_per_arm"] == 1
    assert report["analytical"]["bit_complexity_upper_bound"] is None
    assert report["unknown"]
