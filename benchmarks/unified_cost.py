"""Fail-closed, paired exact-solver cost experiment.

Each measurement runs in its own process. Untouched timing and observed timing
are deliberately distinct measurements; traced execution is not baseline speed.
No observed event count is represented as a universal bit-operation bound.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import json
import os
from pathlib import Path
import platform
import resource
from statistics import median
import subprocess
import sys
from time import perf_counter_ns
import tracemalloc
from typing import Any

from benchmarks.recursive_cases import IDS, VARIANTS, get_case
from scripts.evidence import fingerprints, git_provenance, native_binaries

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "1.0.0"
# The deformation-only case does not execute ContractionEngine.contract and
# cannot be compared as though it had a normal recursive frame.
CASES = tuple(name for name in IDS if name != "crossing-4wire")
UNKNOWN_COSTS = (
    "internal elementary/bit operations inside native Cython kernels",
    "integer operand bit lengths and bit-operation counts at all oracle boundaries",
    "hidden computational costs of user-defined tensor/packet oracles",
    "native allocations and Python allocator retained memory",
    "exclusive wall time per recursive frame and per algorithmic phase",
    "uniform worst-case bit-operation recurrence and non-refusal",
)


def rss_bytes() -> int:
    """Linux ru_maxrss reports KiB, including runtime/import baseline."""
    return int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss) * 1024


def sample_once(case_id: str, variant: str, mode: str) -> dict[str, Any]:
    if case_id not in CASES or variant not in VARIANTS or mode not in ("baseline", "observed"):
        raise ValueError("Unknown case, variant, or measurement mode")
    from non_exponential_sudoku import ContractionEngine, CostLedger, WorkTrace

    case = get_case(case_id, variant)
    ledger = CostLedger(observe_operand_bits=True) if mode == "observed" else None
    trace = WorkTrace() if mode == "observed" else None
    engine = ContractionEngine(case.config, cost_ledger=ledger, work_trace=trace)
    if mode == "observed":
        tracemalloc.start()
    start = perf_counter_ns()
    try:
        actual = engine.contract(case.network)[0]
    finally:
        elapsed_ns = perf_counter_ns() - start
        traced = tracemalloc.get_traced_memory()[1] if tracemalloc.is_tracing() else None
        if tracemalloc.is_tracing():
            tracemalloc.stop()
    if actual != case.expected:
        raise AssertionError(f"{case_id}/{variant}: {actual} != {case.expected}")
    report = ledger.report() if ledger is not None else None
    if report is not None and (not report["frame_tree_reconciled"]
                               or report["truncation"]["frames"]
                               or report["truncation"]["centers"]):
        raise AssertionError("Incomplete or unreconciled cost-ledger evidence")
    return {
        "schema_version": SCHEMA, "status": "verified", "case": case_id,
        "variant": variant, "mode": mode, "exact_count": actual,
        "expected": case.expected, "parameters": case.parameters,
        "duration_ns": elapsed_ns, "peak_process_rss_bytes": rss_bytes(),
        "tracemalloc_peak_bytes": traced,
        "counters": asdict(engine.stats) if report is not None else None,
        "cost_ledger": report, "work_trace": trace.report() if trace is not None else None,
        "measurement_scope": {
            "duration": "single contraction, no case preparation; instrumentation included only in observed",
            "rss": "whole worker process high-water mark; imports and allocator baseline included",
            "tracemalloc": "Python-tracked peak during contraction; not native allocations",
        },
    }


def worker(case_id: str, variant: str, mode: str) -> int:
    try:
        record = sample_once(case_id, variant, mode)
    except Exception as exc:
        record = {"schema_version": SCHEMA, "case": case_id, "variant": variant,
                  "mode": mode, "status": "failed", "error": f"{type(exc).__name__}: {exc}"}
    print(json.dumps(record, sort_keys=True))
    return 0 if record["status"] == "verified" else 1


def _run_worker(case_id: str, variant: str, mode: str, timeout: float) -> dict[str, Any]:
    command = [sys.executable, "-m", "benchmarks.unified_cost", "--worker",
               "--case", case_id, "--variant", variant, "--mode", mode]
    try:
        proc = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                              timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return {"case": case_id, "variant": variant, "mode": mode,
                "status": "timeout", "timeout_seconds": timeout}
    if proc.returncode:
        return {"case": case_id, "variant": variant, "mode": mode,
                "status": "failed", "exit_code": proc.returncode,
                "error": proc.stderr[-2000:] or proc.stdout[-2000:]}
    try:
        row = json.loads(proc.stdout)
    except ValueError:
        return {"case": case_id, "variant": variant, "mode": mode,
                "status": "malformed", "error": proc.stdout[-2000:]}
    if (row.get("status") != "verified" or row.get("case") != case_id
            or row.get("variant") != variant or row.get("mode") != mode
            or row.get("exact_count") != row.get("expected")
            or not isinstance(row.get("duration_ns"), int)
            or row["duration_ns"] <= 0):
        return {"case": case_id, "variant": variant, "mode": mode,
                "status": "invalid", "worker": row}
    return row


def aggregate(rows: list[dict[str, Any]], repeats: int) -> dict[str, Any]:
    """Reject any missing, failed or mismatched arm. Do not invent samples."""
    if repeats < 1 or len(rows) != repeats * 2:
        raise ValueError("Paired sample count mismatch")
    arms: dict[str, list[dict[str, Any]]] = {"baseline": [], "observed": []}
    for row in rows:
        mode = row.get("mode")
        if mode not in arms or row.get("status") != "verified":
            raise ValueError("Missing, refused, failed, or invalid worker sample")
        arms[mode].append(row)
    if any(len(arm) != repeats for arm in arms.values()):
        raise ValueError("Unbalanced measurement arms")
    counts = {row["exact_count"] for row in rows}
    cases = {row["case"] for row in rows}
    variants = {row["variant"] for row in rows}
    if len(counts) != 1 or len(cases) != 1 or len(variants) != 1:
        raise ValueError("Paired exact answer or workload identity mismatch")
    def stats(mode: str) -> dict[str, Any]:
        samples = arms[mode]
        return {"median_duration_ns": median(row["duration_ns"] for row in samples),
                "duration_ns": [row["duration_ns"] for row in samples],
                "peak_process_rss_bytes": [row["peak_process_rss_bytes"] for row in samples],
                "tracemalloc_peak_bytes": [row["tracemalloc_peak_bytes"] for row in samples]}
    base, observed = stats("baseline"), stats("observed")
    return {
        "case": rows[0]["case"], "variant": rows[0]["variant"],
        "exact_count": rows[0]["exact_count"], "repetitions_per_arm": repeats,
        "baseline": base, "observed": observed,
        "instrumentation_walltime_ratio": observed["median_duration_ns"] / base["median_duration_ns"],
        "interpretation": "separate fresh processes; medians are diagnostic, not paired causal estimates",
    }


def run(cases: list[str], variants: list[str], repeats: int, timeout: float) -> dict[str, Any]:
    if repeats < 1 or timeout <= 0 or not cases or not variants:
        raise ValueError("Invalid experiment settings")
    if len(set(cases)) != len(cases) or any(c not in CASES for c in cases):
        raise ValueError("Invalid or duplicate cases")
    if len(set(variants)) != len(variants) or any(v not in VARIANTS for v in variants):
        raise ValueError("Invalid or duplicate variants")
    source_before = fingerprints()
    git_before = git_provenance()
    binaries_before = native_binaries()
    output: dict[str, Any] = {
        "schema_version": SCHEMA, "status": "incomplete",
        "source": source_before, "git": git_before, "native_binaries": binaries_before,
        "environment": {"python": sys.version, "platform": platform.platform(),
                        "cpu_count": os.cpu_count(), "pid": os.getpid()},
        "settings": {"cases": cases, "variants": variants,
                     "repetitions_per_arm": repeats, "worker_timeout_seconds": timeout},
        "measured": [], "analytical": {
            "recurrence": "observed frame call tree reconciled by CostLedger; finite instances only",
            "bit_complexity_upper_bound": None, "uniform_non_refusal": False,
        },
        "unknown": list(UNKNOWN_COSTS),
    }
    for case_id in cases:
        for variant in variants:
            samples = []
            for i in range(repeats):
                # Alternate execution order; never alternate modes inside one worker.
                for mode in (("baseline", "observed") if i % 2 == 0
                             else ("observed", "baseline")):
                    row = _run_worker(case_id, variant, mode, timeout)
                    samples.append(row)
                    if row["status"] != "verified":
                        output["failed_sample"] = row
                        output["status"] = "failed"
                        return output
            output["measured"].append({"summary": aggregate(samples, repeats),
                                        "raw_samples": samples})
    stable = (source_before == fingerprints() and git_before == git_provenance()
              and binaries_before == native_binaries())
    output["inputs_stable"] = stable
    output["status"] = "complete" if stable else "failed_input_drift"
    return output


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--case", default="parity-2wire")
    parser.add_argument("--variant", default="reference")
    parser.add_argument("--mode", choices=("baseline", "observed"), default="baseline")
    parser.add_argument("--cases", nargs="+", default=list(CASES))
    parser.add_argument("--variants", nargs="+", default=["reference"])
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=90)
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/unified-cost.json")
    args = parser.parse_args()
    if args.worker:
        return worker(args.case, args.variant, args.mode)
    try:
        result = run(args.cases, args.variants, args.repeats, args.timeout)
    except Exception as exc:
        result = {"schema_version": SCHEMA, "status": "failed",
                  "error": f"{type(exc).__name__}: {exc}"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Unified cost study: {result['status']}; {args.output}")
    return 0 if result["status"] == "complete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
