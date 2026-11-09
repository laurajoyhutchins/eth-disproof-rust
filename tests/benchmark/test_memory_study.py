"""Measurement contracts: exactness, fresh process isolation, fail-closed evidence."""
from __future__ import annotations

import json
import subprocess
import sys

import pytest

from benchmarks.memory_study import (
    CASES, MemorySample, aggregate_samples, prepare_case, sample_once,
    validate_sample,
)

@pytest.mark.checkpoint
def test_cases_have_stable_labels_and_independent_expected_results() -> None:
    assert len(CASES) == len(set(CASES))
    for case_id in CASES:
        run, expected, description, estimates = prepare_case(case_id)
        assert callable(run)
        assert isinstance(expected, int) and expected > 0
        assert isinstance(description, str) and description
        assert callable(estimates)


@pytest.mark.integration
@pytest.mark.parametrize("case_id", ["leaf.lookup", "leaf.indexed", "mode.grid3",
                                      "nested.jet", "recursive.nested"])
def test_measurements_preserve_exact_result_and_observe_peak(case_id: str) -> None:
    sample = sample_once(case_id)
    validate_sample(sample, case_id=case_id)
    assert sample.status == "verified"
    assert sample.actual == sample.expected
    assert sample.memory["python_tracemalloc_peak_bytes"] >= 0
    assert sample.memory["rss_high_water_bytes"] >= sample.memory["rss_before_bytes"]
    assert sample.memory["rss_high_water_bytes"] >= sample.memory["rss_after_bytes"]
    assert sample.memory["python_tracemalloc_peak_bytes"] >= sample.memory["python_tracemalloc_end_bytes"]


@pytest.mark.checkpoint
def test_invalid_or_incomplete_samples_are_never_comparable() -> None:
    valid = sample_once("leaf.lookup")
    raw = valid.to_dict()
    for changed in (
        {"status": "capacity_refused"},
        {"actual": valid.expected + 1},
        {"memory": {**raw["memory"], "rss_high_water_bytes": -1}},
    ):
        broken = MemorySample.from_dict({**raw, **changed})
        with pytest.raises(ValueError):
            validate_sample(broken, case_id="leaf.lookup")
    with pytest.raises(ValueError):
        aggregate_samples({"leaf.lookup": [valid]}, required=CASES)


@pytest.mark.checkpoint
def test_json_worker_is_fresh_and_machine_readable() -> None:
    result = subprocess.run(
        [sys.executable, "-m", "benchmarks.memory_study", "--worker",
         "--case", "leaf.indexed"],
        capture_output=True, text=True, timeout=25, check=False,
    )
    assert result.returncode == 0, result.stderr
    lines = result.stdout.strip().splitlines()
    assert len(lines) == 1
    record = MemorySample.from_dict(json.loads(lines[0]))
    validate_sample(record, case_id="leaf.indexed")
    assert record.memory["rss_high_water_bytes"] > 0
