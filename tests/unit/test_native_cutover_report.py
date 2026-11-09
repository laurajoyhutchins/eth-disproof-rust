"""Pure-Python tests for benchmark pairing and fail-closed evidence."""
from __future__ import annotations

import json
from pathlib import Path
import pytest
from scripts.native_cutover_report import PAIRS, results_from, paired_report

pytestmark = pytest.mark.checkpoint

def _input(tmp_path: Path, *, missing: bool = False, invalid: bool = False) -> Path:
    cases = {(case, ref) for case, ref, _, _ in PAIRS} | {(case, native) for case, _, native, _ in PAIRS}
    if missing:
        cases.remove(("sparse-grid3", "cython"))
    records = []
    for case, variant in sorted(cases):
        data = ([0.0] * 6 if invalid and variant == "cython" else
                [0.9] * 6 if variant in ("python", "reference") else [0.5] * 6)
        records.append({"extra_info": {"benchmark.case": case,
                                       "benchmark.variant": variant},
                        "stats": {"data": data}})
    path = tmp_path / "timing.json"
    path.write_text(json.dumps({"benchmarks": records}))
    return path

def test_benchmarks_are_paired_and_report_a_ratio(tmp_path: Path) -> None:
    report = paired_report(results_from([_input(tmp_path)]))
    assert len(report["pairs"]) == len(PAIRS)
    assert report["families"]["packet-evaluation"]["all_cases_20pct_faster"]
    assert report["pairs"][0]["speedup"] == pytest.approx(1.8)

def test_missing_pair_fails_closed(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="Missing paired"):
        paired_report(results_from([_input(tmp_path, missing=True)]))

def test_invalid_timing_fails_closed(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="invalid samples"):
        results_from([_input(tmp_path, invalid=True)])
