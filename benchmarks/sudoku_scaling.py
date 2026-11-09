"""Bounded full-input generalized Sudoku scaling experiment.

All cases are supplied to each backend as Sudoku givens, never hidden witness
restrictions. Exact answers are independently checked with bounded MRV search.
Capacity refusal and timeout are measurements of noncompletion, not solutions.
"""
from __future__ import annotations

import argparse
from collections import Counter
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

from reference.generalized_bench import canonical_solution
from reference.mrv_count import count_mrv_reference
from reference.real_sudoku_bench import puzzles
from scripts.evidence import fingerprints, git_provenance, native_binaries
from non_exponential_sudoku.sudoku.three_cnf import Puzzle

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "1.0.0"
ALGORITHMS = ("frontier", "paper")
MODES = ("baseline", "observed")


def fixtures() -> dict[str, tuple[Puzzle, int | None]]:
    """Full boards, including an unconstrained 4x4 and increasing real clues."""
    original = {name: (puzzle, expected) for name, puzzle, expected in puzzles()}
    original["4x4-empty"] = (Puzzle(2, (0,) * 16), 288)
    # Eight missing cells in a 16x16 solved grid. Expected count comes only
    # from the independent MRV oracle, not the generating solution.
    solved = list(canonical_solution(4))
    for cell in (0, 8, 32, 40, 128, 136, 160, 168):
        solved[cell] = 0
    original["16x16-248-givens-eight-holes"] = (Puzzle(4, tuple(solved)), None)
    return original


DEFAULT_CASES = (
    "4x4-empty", "4x4-8-givens-four-solutions",
    "9x9-73-givens-four-solutions", "9x9-hard-unique",
    "16x16-252-givens-two-solutions", "16x16-248-givens-eight-holes",
)


def _rss() -> int:
    return int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss) * 1024


def sample(case: str, algorithm: str, mode: str, max_oracle_nodes: int) -> dict[str, Any]:
    if case not in fixtures() or algorithm not in ALGORITHMS or mode not in MODES:
        raise ValueError("Unknown case, algorithm or mode")
    if max_oracle_nodes < 1:
        raise ValueError("Oracle node limit must be positive")
    puzzle, declared = fixtures()[case]
    descriptor = {
        "case": case, "algorithm": algorithm, "mode": mode, "side": puzzle.side,
        "box_side": puzzle.b, "cells": puzzle.side ** 2,
        "givens": sum(bool(x) for x in puzzle.entries),
        "blank_cells": sum(not x for x in puzzle.entries),
        "expected_from_fixture": declared, "max_oracle_nodes": max_oracle_nodes,
    }
    t_oracle = perf_counter_ns()
    try:
        expected, oracle_nodes = count_mrv_reference(puzzle, max_nodes=max_oracle_nodes)
    except RuntimeError as exc:
        return {**descriptor, "status": "oracle_refusal", "oracle_error": str(exc),
                "oracle_duration_ns": perf_counter_ns() - t_oracle,
                "exact_count": None, "elapsed_ns": None}
    oracle_ns = perf_counter_ns() - t_oracle
    if declared is not None and expected != declared:
        raise AssertionError(f"Independent MRV disagrees with declared count: {case}")
    from non_exponential_sudoku import (ContractionEngine, ContractorConfig,
                                       CostLedger, LeafConfig, WorkTrace)
    from non_exponential_sudoku.runtime.budget import CapacityError
    from non_exponential_sudoku.sudoku.frontier import (count_frontier,
            FrontierLimits, FrontierCapacityError)
    from reference.local_support import pin_band_wires, LocalContradiction

    ledger = CostLedger(max_frames=5_000, max_centers=5_000, observe_operand_bits=True) if mode == "observed" and algorithm == "paper" else None
    trace = WorkTrace() if ledger is not None else None
    stats: dict[str, Any] | None = None
    reduction: dict[str, Any] | None = None
    outcome = "verified"
    refusal_reason: str | None = None
    actual: int | None = None
    engine = None
    if mode == "observed":
        tracemalloc.start()
    start = perf_counter_ns()
    try:
        if algorithm == "frontier":
            response = count_frontier(puzzle, limits=FrontierLimits(
                max_states=20_000, max_transitions=500_000,
                max_estimated_bytes=32 * 1024 * 1024))
            actual = response.count
            stats = asdict(response.stats)
        else:
            try:
                network, reduction = pin_band_wires(puzzle)
            except LocalContradiction:
                actual = 0
                reduction = {"contradiction_detected": True}
            else:
                engine = ContractionEngine(
                    ContractorConfig(max(1, network.edges), network.edges + 1,
                        schedule="paper", leaf=LeafConfig(limit=18, strategy="eliminate")),
                    cost_ledger=ledger, work_trace=trace)
                actual = engine.contract(network)[0]
                stats = asdict(engine.stats)
    except (CapacityError, FrontierCapacityError) as exc:
        outcome = "capacity_refusal"
        refusal_reason = f"{type(exc).__name__}: {exc}"
        if engine is not None:
            stats = asdict(engine.stats)
    finally:
        elapsed = perf_counter_ns() - start
        peak_python = tracemalloc.get_traced_memory()[1] if tracemalloc.is_tracing() else None
        if tracemalloc.is_tracing():
            tracemalloc.stop()

    if outcome == "verified" and actual != expected:
        raise AssertionError(f"Incorrect count for {case}/{algorithm}: {actual} != {expected}")
    evidence = ledger.report() if ledger is not None else None
    if evidence is not None and (evidence["truncation"]["frames"]
                                  or evidence["truncation"]["centers"]
                                  or not evidence["frame_tree_reconciled"]):
        raise AssertionError("Truncated or unreconciled paper cost evidence")
    return {
        **descriptor, "status": outcome, "expected_count": expected,
        "oracle_nodes": oracle_nodes, "oracle_duration_ns": oracle_ns,
        "exact_count": actual, "refusal_reason": refusal_reason,
        "elapsed_ns": elapsed, "peak_process_rss_bytes": _rss(),
        "tracemalloc_peak_bytes": peak_python,
        "algorithm_stats": stats, "reduction": reduction,
        "ledger": evidence, "work_trace": trace.report() if trace is not None else None,
        "semantics": {
            "elapsed": "whole counting path from original givens, excluding fixture and independent MRV",
            "rss": "fresh Linux process high water, includes imports and runtime",
            "tracemalloc": "observed Python allocations, not native allocations",
            "refusal": "no count was produced; neither zero nor a successful solve",
        },
    }


def _worker(case: str, algorithm: str, mode: str, max_oracle_nodes: int) -> int:
    try:
        row = sample(case, algorithm, mode, max_oracle_nodes)
    except Exception as exc:
        row = {"case": case, "algorithm": algorithm, "mode": mode,
               "status": "failed", "error": f"{type(exc).__name__}: {exc}"}
    print(json.dumps(row, sort_keys=True))
    # Explicit oracle/solver capacity refusal is a measurement, not a crash.
    return 0 if row["status"] in ("verified", "capacity_refusal", "oracle_refusal") else 1


def _bounded_worker(case: str, algorithm: str, mode: str,
                    max_oracle_nodes: int, timeout: float) -> dict[str, Any]:
    try:
        proc = subprocess.run(
            [sys.executable, "-m", "benchmarks.sudoku_scaling", "--worker",
             "--case", case, "--algorithm", algorithm, "--mode", mode,
             "--max-oracle-nodes", str(max_oracle_nodes)],
            cwd=ROOT, capture_output=True, text=True, timeout=timeout, check=False,
        )
    except subprocess.TimeoutExpired:
        return {"case": case, "algorithm": algorithm, "mode": mode,
                "status": "timeout", "timeout_seconds": timeout}
    if proc.returncode:
        return {"case": case, "algorithm": algorithm, "mode": mode,
                "status": "failed", "exit_code": proc.returncode,
                "error": proc.stdout[-2000:] + proc.stderr[-2000:]}
    try:
        row = json.loads(proc.stdout)
    except ValueError:
        return {"case": case, "algorithm": algorithm, "mode": mode,
                "status": "malformed", "error": proc.stdout[-2000:]}
    if (not isinstance(row, dict) or row.get("case") != case
            or row.get("algorithm") != algorithm or row.get("mode") != mode
            or row.get("status") not in ("verified", "capacity_refusal", "oracle_refusal")
            or (row.get("status") == "verified" and
                (row.get("exact_count") != row.get("expected_count")
                 or not isinstance(row.get("elapsed_ns"), int)
                 or row["elapsed_ns"] <= 0))
            or (row.get("status") != "verified" and row.get("exact_count") is not None)):
        return {"case": case, "algorithm": algorithm, "mode": mode,
                "status": "invalid", "data": row}
    return row


def summarize(rows: list[dict[str, Any]], repeats: int) -> dict[str, Any]:
    if len(rows) != 2 * repeats:
        raise ValueError("Missing paired observations")
    for mode in MODES:
        arm = [r for r in rows if r.get("mode") == mode]
        if len(arm) != repeats:
            raise ValueError("Missing measurement arm")
        if any(row.get("status") in ("failed", "invalid", "malformed") for row in arm):
            raise ValueError("Failed or malformed worker")
        if len({row["status"] for row in arm}) != 1:
            raise ValueError("Nonreproducible result status within an arm")
    outcome_set = {row["status"] for row in rows}
    if len(outcome_set) != 1:
        raise ValueError("Baseline and instrumented outcomes disagree")
    outcome = outcome_set.pop()
    if outcome == "verified":
        expected_set = {row["expected_count"] for row in rows}
        actual_set = {row["exact_count"] for row in rows}
        if len(expected_set) != 1 or expected_set != actual_set:
            raise ValueError("Inconsistent exact counts across samples")
    def observed_median(mode: str, field: str) -> float | None:
        values = [row.get(field) for row in rows if row["mode"] == mode]
        if not values or any(type(v) is not int or v < 0 for v in values):
            return None
        return float(median(values))
    duration_by_arm = {mode: observed_median(mode, "elapsed_ns") for mode in MODES}
    rss_by_arm = {mode: observed_median(mode, "peak_process_rss_bytes") for mode in MODES}
    python_peak = observed_median("observed", "tracemalloc_peak_bytes")
    if (outcome == "verified" and duration_by_arm["baseline"] is not None
            and duration_by_arm["observed"] is not None
            and duration_by_arm["baseline"] > 0):
        overhead: float | None = (
            duration_by_arm["observed"] / duration_by_arm["baseline"])
    else:
        overhead = None
    return {
        "case": rows[0]["case"], "algorithm": rows[0]["algorithm"],
        "outcome": outcome, "repeats_per_arm": repeats,
        "median_duration_ns_by_arm": duration_by_arm,
        "median_peak_process_rss_bytes_by_arm": rss_by_arm,
        "median_python_traced_peak_bytes": python_peak,
        "instrumentation_walltime_ratio": overhead,
        "answer_verified": outcome == "verified",
        "reporting_note": "time measures time to outcome; refusal is not a Sudoku solution or complexity bound",
    }


def run(cases: list[str], algorithms: list[str], repeats: int,
        timeout: float, max_oracle_nodes: int) -> dict[str, Any]:
    all_cases = fixtures()
    if (not cases or not algorithms or len(set(cases)) != len(cases)
            or len(set(algorithms)) != len(algorithms)
            or any(c not in all_cases for c in cases)
            or any(a not in ALGORITHMS for a in algorithms)
            or repeats < 1 or timeout <= 0 or max_oracle_nodes < 1):
        raise ValueError("Invalid experiment configuration")
    before = fingerprints()
    git = git_provenance()
    natives = native_binaries()
    result: dict[str, Any] = {
        "schema_version": SCHEMA, "status": "incomplete",
        "source": before, "git": git, "native_binaries": natives,
        "platform": {"python": sys.version, "os": platform.platform(), "cpu_count": os.cpu_count()},
        "settings": {"cases": cases, "algorithms": algorithms, "repeats": repeats,
                     "timeout_seconds_per_worker": timeout, "max_oracle_nodes": max_oracle_nodes},
        "measurements": [], "outcome_counts": {},
        "analytical": {"worst_case_bit_bound": None,
                       "paper_schedule_non_refusal": False,
                       "frontier_reachable_width_bound": "exponential in frontier width"},
        "unknown": [
            "native arithmetic bit-operation costs",
            "uniform recursive oracle costs and operand lengths",
            "generalized Sudoku worst-case asymptotic scaling",
            "exclusive per-phase and per-frame execution time",
        ],
    }
    counts: Counter[str] = Counter()
    for case in cases:
        for algorithm in algorithms:
            samples: list[dict[str, Any]] = []
            for repeat in range(repeats):
                for mode in (MODES if repeat % 2 == 0 else tuple(reversed(MODES))):
                    sample_data = _bounded_worker(case, algorithm, mode, max_oracle_nodes, timeout)
                    samples.append(sample_data)
            try:
                summary = summarize(samples, repeats)
            except ValueError as exc:
                result["status"] = "failed"
                result["failed_comparison"] = {"case": case, "algorithm": algorithm,
                                                "reason": str(exc), "samples": samples}
                return result
            counts[summary["outcome"]] += 1
            result["measurements"].append({"summary": summary, "raw_samples": samples})
    result["outcome_counts"] = dict(sorted(counts.items()))
    result["inputs_stable"] = (before == fingerprints()
                               and git == git_provenance()
                               and natives == native_binaries())
    result["status"] = "complete" if result["inputs_stable"] else "failed_input_drift"
    result["all_cases_solved"] = counts["verified"] == len(cases) * len(algorithms)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--case", default="4x4-empty")
    parser.add_argument("--algorithm", choices=ALGORITHMS, default="frontier")
    parser.add_argument("--mode", choices=MODES, default="baseline")
    parser.add_argument("--cases", nargs="+", default=list(DEFAULT_CASES))
    parser.add_argument("--algorithms", nargs="+", default=list(ALGORITHMS))
    parser.add_argument("--repeats", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=20)
    parser.add_argument("--max-oracle-nodes", type=int, default=200_000)
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/sudoku-scaling.json")
    args = parser.parse_args()
    if args.worker:
        return _worker(args.case, args.algorithm, args.mode, args.max_oracle_nodes)
    try:
        report = run(args.cases, args.algorithms, args.repeats,
                     args.timeout, args.max_oracle_nodes)
    except Exception as exc:
        report = {"schema_version": SCHEMA, "status": "failed",
                  "error": f"{type(exc).__name__}: {exc}"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"Full-input Sudoku scaling: {report['status']}; {args.output}")
    return 0 if report["status"] == "complete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
