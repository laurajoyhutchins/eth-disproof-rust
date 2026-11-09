"""Summarize paired, correctness-gated native/Python benchmarks.

Only compare identical benchmark case IDs. This report is not an
automatic production dispatcher.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from statistics import median
from typing import Any

PAIRS: tuple[tuple[str, str, str, str], ...] = (
    ("sparse-grid3", "python", "cython", "sparse-elimination"),
    ("sparse-grid4", "python", "cython", "sparse-elimination"),
    ("dense-grid3", "python", "cython", "sparse-elimination"),
    ("parity-2wire", "reference", "packet", "packet-evaluation"),
    ("sudoku-4wire", "reference", "packet", "packet-evaluation"),
    ("sudoku-8wire", "reference", "packet", "packet-evaluation"),
    ("nested-2wire", "reference", "packet", "packet-evaluation"),
    ("crossing-4wire", "reference", "packet", "packet-evaluation"),
    ("parity-2wire", "reference", "leaf", "leaf-elimination"),
    ("sudoku-4wire", "reference", "leaf", "leaf-elimination"),
    ("sudoku-8wire", "reference", "leaf", "leaf-elimination"),
    ("nested-2wire", "reference", "leaf", "leaf-elimination"),
    ("crossing-4wire", "reference", "leaf", "leaf-elimination"),
)

def results_from(files: list[Path]) -> dict[tuple[str, str], dict[str, Any]]:
    results: dict[tuple[str, str], dict[str, Any]] = {}
    for file in files:
        data = json.loads(file.read_text())
        benchmarks = data.get("benchmarks", [])
        if not isinstance(benchmarks, list) or not benchmarks:
            raise ValueError(f"Missing benchmark cases: {file}")
        for entry in benchmarks:
            info = entry.get("extra_info", {})
            case, variant = info.get("benchmark.case"), info.get("benchmark.variant")
            if not isinstance(case, str) or not isinstance(variant, str):
                raise ValueError(f"Benchmark missing case/variant metadata: {entry.get('name')}")
            key = case, variant
            if key in results:
                raise ValueError(f"Duplicate case/variant: {key}")
            stats = entry["stats"]
            values = stats.get("data", [])
            if not values or not all(isinstance(x, (int, float)) and math.isfinite(x) and x > 0 for x in values):
                raise ValueError(f"Missing or invalid samples for {key}")
            results[key] = {
                "median_s": median(values),
                "min_s": min(values),
                "max_s": max(values),
                "samples": len(values),
                "duration_s": values,
            }
    return results

def paired_report(results: dict[tuple[str, str], dict[str, Any]]) -> dict[str, Any]:
    pairs = []
    for case, python_variant, native_variant, family in PAIRS:
        left = results.get((case, python_variant))
        right = results.get((case, native_variant))
        if left is None or right is None:
            raise ValueError(f"Missing paired measurement: {case}, {python_variant}/{native_variant}")
        if left["samples"] < 5 or right["samples"] < 5:
            raise ValueError(f"Too few benchmark samples for {case}")
        speedup = left["median_s"] / right["median_s"]
        pairs.append({
            "case": case, "family": family,
            "python_variant": python_variant,
            "native_variant": native_variant,
            "python": left, "native": right,
            "speedup": speedup,
            "candidate": speedup >= 1.20,
        })
    families: dict[str, dict[str, Any]] = {}
    for family in sorted({p["family"] for p in pairs}):
        cases = [p for p in pairs if p["family"] == family]
        eligible = all(p["candidate"] for p in cases)
        families[family] = {
            "all_cases_20pct_faster": eligible,
            "slowest_speedup": min(p["speedup"] for p in cases),
            "fastest_speedup": max(p["speedup"] for p in cases),
            "status": "candidate_for_deeper_review" if eligible else "retain_current_dispatch",
        }
    return {
        "schema_version": 1,
        "metric": "median wall-clock duration; speedup=python/native",
        "gate": "A 1.20x median win in each case indicates further review, NOT automated default change",
        "pairs": pairs, "families": families,
    }

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    report = paired_report(results_from(args.inputs))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("case | Python median (ms) | Native median (ms) | Python/native")
    print("--- | ---: | ---: | ---:")
    for pair in report["pairs"]:
        print(f"{pair['case']} / {pair['family']} | {pair['python']['median_s'] * 1000:.3f} | {pair['native']['median_s'] * 1000:.3f} | {pair['speedup']:.2f}x")
    print("\nFamily decisions (candidates only):")
    for family, data in report["families"].items():
        print(f"{family}: {data['status']} (minimum observed speedup {data['slowest_speedup']:.2f}x)")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
