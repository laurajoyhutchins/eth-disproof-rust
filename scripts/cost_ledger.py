#!/usr/bin/env python3
"""Emit an observed contraction cost ledger for a reproducible recursive case.

Example:
  python scripts/cost_ledger.py nested-2wire --variant reference --output artifacts/nested-ledger.json

The JSON is an operation trace, not a subexponential complexity certificate.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT))

from scripts.evidence import fingerprints, git_provenance, native_binaries  # noqa: E402
from benchmarks.recursive_cases import get_case  # noqa: E402
from non_exponential_sudoku import ContractionEngine, CostLedger  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", choices=["parity-2wire", "nested-2wire",
                                          "sudoku-4wire", "sudoku-8wire"])
    parser.add_argument("--variant", default="reference", choices=[
        "reference", "plans", "packet", "leaf", "combined", "memo", "memo-all"])
    parser.add_argument("--max-frames", type=int, default=20_000)
    parser.add_argument("--max-centers", type=int, default=20_000)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    source_before = fingerprints()
    git_before = git_provenance()
    native_before = native_binaries()
    case = get_case(args.case, args.variant)
    ledger = CostLedger(max_frames=args.max_frames, max_centers=args.max_centers)
    engine = ContractionEngine(case.config, cost_ledger=ledger)
    result: int | None = None
    error: str | None = None
    try:
        actual = engine.contract(case.network)[0]
        if not isinstance(actual, int):
            error = f"expected integer count, got {type(actual).__name__}"
        else:
            result = actual
            if result != case.expected:
                error = f"wrong exact result: expected {case.expected}, got {result}"
    except Exception as exc:
        error = f"{type(exc).__name__}: {exc}"
    source_after = fingerprints()
    git_after = git_provenance()
    native_after = native_binaries()
    inputs_stable = (source_before == source_after and
                     git_before == git_after and native_before == native_after)
    if not inputs_stable:
        error = "Source, Git state, or native binaries changed during measurement"
    report = {
        "case": args.case, "variant": args.variant,
        "expected_exact_count": case.expected, "observed_exact_count": result,
        "passed": error is None, "error": error,
        "solver_counters": asdict(engine.stats), "cost_ledger": ledger.report(),
        "git": git_before, **source_before,
        "native_extensions": native_before, "inputs_stable": inputs_stable,
        "inputs_after": {"git": git_after, **source_after,
                         "native_extensions": native_after} if not inputs_stable else None,
        "case_definition": "benchmarks/recursive_cases.py:get_case",
        "config": asdict(case.config),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"case={args.case} variant={args.variant} passed={error is None}"
          f" calls={ledger.frames_observed} centers={ledger.centers_observed}"
          f" output={args.output}", flush=True)
    return 0 if error is None else 1


if __name__ == "__main__":
    raise SystemExit(main())
