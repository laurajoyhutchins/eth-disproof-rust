"""Full-path bounded CNF scaling, separating exact counts and noncompletion.

Each fresh worker builds a CNF formula and analytically verifies its exact
count (also independently brute-force checks small n) before entering the
measured production pipeline. Both original separated-Taylor tuple counting
and optional exact factor elimination use the SAME `count_cnf_reference`.
A timeout or capacity refusal never becomes a completed count or a speedup.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, dataclass
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
from typing import Any, Literal

from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
from non_exponential_sudoku.eth.pipeline import (
    ReferencePipelineConfig, count_cnf_reference,
)
from non_exponential_sudoku.eth.sparsification import reference_sparsification_parameters
from non_exponential_sudoku.runtime.budget import CapacityError
from scripts.evidence import fingerprints, git_provenance, native_binaries


ROOT = Path(__file__).resolve().parents[2]
SCHEMA = "1.0.0"
FAMILIES = ("path", "matching", "xor_pairs", "clique")
SUMMATIONS = ("tuples", "eliminate", "fused", "multilinear")
MODES = ("baseline", "observed")
DEFAULT_FAMILIES = ("path", "matching", "clique")
DEFAULT_SIZES = (2, 4, 6)


@dataclass(frozen=True, slots=True)
class Scenario:
    family: str
    nvars: int
    formula: CNFFormula
    expected_count: int
    oracle: str


def _fibonacci(index: int) -> int:
    a, b = 0, 1
    for _ in range(index):
        a, b = b, a + b
    return a


def scenario(family: str, n: int) -> Scenario:
    """Independent closed-form counts, tested against exhaustive small n.

    Positive (x_i OR x_(i+1)) paths have F_(n+2) models. A positive
    pairwise clique allows at most one false variable, hence n+1 models.
    Disjoint OR pairs have 3^(n/2); disjoint XOR pairs have 2^(n/2).
    """
    if (family not in FAMILIES or type(n) is not int or not 2 <= n <= 64
            or family in ("matching", "xor_pairs") and n % 2):
        raise ValueError("Unsupported CNF family/size (2..64; pairs need even size)")
    if family == "path":
        clauses = tuple((i, i + 1) for i in range(1, n))
        expected = _fibonacci(n + 2)
    elif family == "clique":
        clauses = tuple((i, j) for i in range(1, n + 1)
                        for j in range(i + 1, n + 1))
        expected = n + 1
    elif family == "matching":
        clauses = tuple((i, i + 1) for i in range(1, n, 2))
        expected = 3 ** (n // 2)
    else:
        clauses = tuple(clause for i in range(1, n, 2)
                        for clause in ((i, i + 1), (-i, -(i + 1))))
        expected = 2 ** (n // 2)
    return Scenario(family, n, CNFFormula(n, clauses), expected, "closed-form")


def _rss_bytes() -> int:
    """On Linux resource.ru_maxrss reports KiB, including interpreter startup."""
    return int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss) * 1024


def _leaf_evidence(leaves: tuple[Any, ...]) -> dict[str, int]:
    """Aggregate only completed mathematical leaves, never partial failures."""
    bases = {v.factor_scope_basis for v in leaves}
    if len(bases) != 1:
        raise ArithmeticError("Inconsistent Taylor factor scope units across leaves")
    return {
        "leaves_completed": len(leaves),
        "factor_scope_basis": next(iter(bases)),
        "max_prepared_variables": max(v.prepared_variables for v in leaves),
        "constructed_leaves": sum(v.method == "certified-construction" for v in leaves),
        "tiny_base_leaves": sum(v.method == "two-assignment-base" for v in leaves),
        "centers": sum(v.centers for v in leaves),
        "taylor_pairs": sum(v.taylor_pairs for v in leaves),
        "measurement_tuples": sum(v.measurement_tuples for v in leaves),
        "factor_assignments_tested": sum(v.factor_assignments_tested for v in leaves),
        "factor_scope_peak": max((v.factor_scope_peak for v in leaves), default=0),
        "factor_entries_peak": max((v.factor_entries_peak for v in leaves), default=0),
        "factor_eliminations": sum(v.factor_eliminations for v in leaves),
        "multilinear_term_products": sum(v.multilinear_term_products for v in leaves),
        "multilinear_support_peak": max((v.multilinear_support_peak for v in leaves), default=0),
        "hermite_operations": sum(v.hermite_operations for v in leaves),
        "max_coefficient_bits": max((v.max_coefficient_bits for v in leaves), default=0),
    }


def sample_once(
    family: str, n: int, summation: str, mode: str, *, threshold: int,
    max_leaves: int, r: int, Q: int, R: int, backend: str,
    oracle_max_vars: int,
) -> dict[str, Any]:
    """Measure the full production path, not construction of an oracle answer."""
    if (summation not in SUMMATIONS or mode not in MODES
            or backend not in ("python", "flint") or oracle_max_vars < 0
            or oracle_max_vars > 20 or threshold < 1):
        raise ValueError("Invalid experiment arguments")
    case = scenario(family, n)
    oracle_checked = case.nvars <= oracle_max_vars
    if oracle_checked:
        observed = count_bruteforce(case.formula, max_variables=oracle_max_vars)
        if observed != case.expected_count:
            raise AssertionError("Independent brute-force oracle disagrees with formula count")

    config = ReferencePipelineConfig(
        sparsification=reference_sparsification_parameters(3, threshold),
        max_leaves=max_leaves, r=r, Q=Q, R=R,
        backend=backend, summation=summation,
    )
    params = {
        "r": r, "Q": Q, "R": R,
        "threshold": threshold, "max_leaves": max_leaves,
        "backend": backend, "summation": summation,
        "parameter_regime": "finite reference, NOT paper schedule admission",
    }
    result = None
    refusal = None
    if mode == "observed":
        tracemalloc.start()
    start = perf_counter_ns()
    try:
        result = count_cnf_reference(case.formula, config=config)
    except CapacityError as exc:
        refusal = f"{type(exc).__name__}: {exc}"
    finally:
        elapsed = max(1, perf_counter_ns() - start)
        traced = tracemalloc.get_traced_memory()[1] if tracemalloc.is_tracing() else None
        if tracemalloc.is_tracing():
            tracemalloc.stop()

    if result is not None and result.count != case.expected_count:
        raise AssertionError(
            f"Wrong exact count: {family}/{n}/{summation}: "
            f"{result.count} != {case.expected_count}"
        )
    completed = result is not None
    return {
        "schema_version": SCHEMA,
        "family": family, "nvars": n, "clauses": len(case.formula.clauses),
        "summation": summation, "mode": mode, "parameters": params,
        "status": "verified" if completed else "capacity_refusal",
        "expected_count": case.expected_count,
        "exact_count": result.count if completed else None,
        "count_bits": result.count.bit_length() if completed else None,
        "oracle": case.oracle,
        "small_bruteforce_oracle_checked": oracle_checked,
        "refusal_reason": refusal,
        "elapsed_ns": elapsed,
        "peak_process_rss_bytes": _rss_bytes(),
        "peak_python_traced_bytes": traced,
        "leaf_evidence": _leaf_evidence(result.leaves) if completed else None,
        "semantic_limits": {
            "duration": "whole exact CNF pipeline excluding formula generation and reference checks",
            "rss": "new process high-water RSS including interpreter/imports",
            "traced_peak": "Python allocations only, not native FLINT/Cython buffers",
            "refusal": "no count; incomplete work intentionally not reported as completed leaves",
        },
    }


def _worker(family: str, n: int, summation: str, mode: str, *,
            threshold: int, max_leaves: int, r: int, Q: int, R: int,
            backend: str, oracle_max_vars: int) -> int:
    try:
        record = sample_once(
            family, n, summation, mode, threshold=threshold,
            max_leaves=max_leaves, r=r, Q=Q, R=R, backend=backend,
            oracle_max_vars=oracle_max_vars,
        )
    except Exception as exc:
        record = {
            "schema_version": SCHEMA, "family": family, "nvars": n,
            "summation": summation, "mode": mode, "status": "failed",
            "exact_count": None, "error": f"{type(exc).__name__}: {exc}",
        }
    print(json.dumps(record, sort_keys=True), flush=True)
    return 0 if record["status"] in ("verified", "capacity_refusal") else 1


def _run_worker(
    family: str, n: int, summation: str, mode: str, *,
    timeout: float, threshold: int, max_leaves: int,
    r: int, Q: int, R: int, backend: str, oracle_max_vars: int,
) -> dict[str, Any]:
    expected = scenario(family, n).expected_count
    command = [
        sys.executable, "-m", "benchmarks.eth.cnf_scaling", "--worker",
        "--family", family, "--nvars", str(n), "--summation", summation,
        "--mode", mode, "--threshold", str(threshold),
        "--max-leaves", str(max_leaves),
        "--r", str(r), "--Q", str(Q), "--R", str(R),
        "--backend", backend, "--oracle-max-vars", str(oracle_max_vars),
    ]
    try:
        proc = subprocess.run(
            command, cwd=ROOT, capture_output=True, text=True,
            timeout=timeout, check=False,
        )
    except subprocess.TimeoutExpired:
        return {
            "family": family, "nvars": n, "summation": summation, "mode": mode,
            "status": "timeout", "timeout_seconds": timeout,
            "expected_count": expected, "exact_count": None,
            "elapsed_ns": None, "peak_process_rss_bytes": None,
            "peak_python_traced_bytes": None,
        }
    if proc.returncode:
        return {
            "family": family, "nvars": n, "summation": summation, "mode": mode,
            "status": "failed", "exit_code": proc.returncode,
            "error": (proc.stderr + "\n" + proc.stdout)[-2000:],
            "expected_count": expected, "exact_count": None,
        }
    try:
        row = json.loads(proc.stdout)
    except (ValueError, TypeError):
        row = {"status": "malformed", "stdout_tail": proc.stdout[-2000:]}
    if (not isinstance(row, dict)
            or row.get("family") != family or row.get("nvars") != n
            or row.get("summation") != summation or row.get("mode") != mode
            or row.get("expected_count") != expected
            or row.get("status") not in ("verified", "capacity_refusal")
            or type(row.get("elapsed_ns")) is not int or row["elapsed_ns"] <= 0
            or (row.get("status") == "verified"
                and (row.get("exact_count") != expected
                     or not isinstance(row.get("leaf_evidence"), dict)))
            or (row.get("status") == "capacity_refusal"
                and (row.get("exact_count") is not None
                     or row.get("leaf_evidence") is not None))):
        return {
            "family": family, "nvars": n, "summation": summation, "mode": mode,
            "status": "invalid", "evidence": row, "exact_count": None,
        }
    return row


def summarize(rows: list[dict[str, Any]], repeats: int) -> dict[str, Any]:
    """Reject mismatched arms and incorrect counts; record bounded refusal."""
    if repeats < 1 or len(rows) != 2 * repeats:
        raise ValueError("Incomplete paired measurements")
    identity = ("family", "nvars", "summation", "expected_count")
    if any(len({str(row.get(key)) for row in rows}) != 1 for key in identity):
        raise ValueError("Mismatched workload or independent exact oracle")
    for mode in MODES:
        if sum(row.get("mode") == mode for row in rows) != repeats:
            raise ValueError("Missing baseline/observed arm")
    allowed = ("verified", "capacity_refusal", "timeout")
    arm_outcomes = {row["mode"]: row.get("status") for row in rows}
    outcomes = {row.get("status") for row in rows}
    if not outcomes.issubset(set(allowed)):
        raise ValueError("Failed or unrecognized worker outcome")
    expected = rows[0]["expected_count"]
    for row in rows:
        if row["status"] == "verified":
            if row.get("exact_count") != expected:
                raise ValueError("Worker exact count disagrees with independent oracle")
        elif row.get("exact_count") is not None:
            raise ValueError("Noncompletion was misreported as an exact count")
    # A baseline completion and traced timeout is a real, useful observation.
    # It is NOT a valid paired speed comparison or a complete verified case.
    # Keep both raw outcomes rather than silently deleting one or inventing
    # a comparable duration.
    outcome = next(iter(outcomes)) if len(outcomes) == 1 else "discordant_outcomes"

    def med(mode: str, field: str) -> float | None:
        values = [row.get(field) for row in rows if row["mode"] == mode]
        if any(type(v) is not int or v < 0 for v in values):
            return None
        return float(median(values))

    times = {mode: med(mode, "elapsed_ns") for mode in MODES}
    rss = {mode: med(mode, "peak_process_rss_bytes") for mode in MODES}
    ratio = (times["observed"] / times["baseline"]
             if outcome == "verified" and times["observed"] is not None
             and times["baseline"] is not None and times["baseline"] > 0
             else None)
    return {
        "family": rows[0]["family"], "nvars": rows[0]["nvars"],
        "summation": rows[0]["summation"],
        "expected_count": expected,
        "outcome": outcome, "answer_verified": outcome == "verified",
        "arm_outcomes": arm_outcomes if repeats == 1 else {
            mode: [row["status"] for row in rows if row["mode"] == mode]
            for mode in MODES
        },
        "repeats_per_arm": repeats,
        "median_duration_ns_by_arm": times,
        "median_process_rss_bytes_by_arm": rss,
        "median_python_traced_peak_bytes": med("observed", "peak_python_traced_bytes"),
        "instrumentation_walltime_ratio": ratio,
        "interpretation": ("discordant outcomes forbid a paired speed comparison"
                           if outcome == "discordant_outcomes" else
                           "medians are per-process observations, not a worst-case bound"),
    }


def run(
    families: list[str], sizes: list[int], summations: list[str], *,
    repeats: int, timeout: float, threshold: int, max_leaves: int,
    r: int, Q: int, R: int, backend: str, oracle_max_vars: int,
) -> dict[str, Any]:
    if (not families or not sizes or not summations or repeats < 1 or timeout <= 0
            or threshold < 1 or max_leaves < 1 or r < 2 or Q < 1 or R < 1
            or R > Q + 1 or backend not in ("python", "flint")
            or not 0 <= oracle_max_vars <= 20
            or len(set(families)) != len(families)
            or len(set(sizes)) != len(sizes)
            or len(set(summations)) != len(summations)
            or any(f not in FAMILIES for f in families)
            or any(s not in SUMMATIONS for s in summations)):
        raise ValueError("Invalid experiment configuration")
    for f in families:
        for n in sizes:
            scenario(f, n)
    before, git, natives = fingerprints(), git_provenance(), native_binaries()
    report: dict[str, Any] = {
        "schema_version": SCHEMA, "status": "incomplete",
        "source": before, "git": git, "native_binaries": natives,
        "platform": {
            "python": sys.version, "os": platform.platform(), "cpu_count": os.cpu_count(),
        },
        "settings": {
            "families": families, "sizes": sizes, "summations": summations,
            "repeats_per_arm": repeats, "timeout_seconds_per_worker": timeout,
            "threshold": threshold, "max_leaves": max_leaves, "r": r, "Q": Q, "R": R,
            "backend": backend, "oracle_max_vars": oracle_max_vars,
            "parameter_regime": "finite reference; NOT manuscript parameters",
        },
        "measurements": [], "outcome_counts": {},
        "analytical": {
            "closed_form_family_exact_counts": True,
            "complete_worst_case_bit_bound": None,
            "general_n_refusal_free": False,
            "subexponential_claim": False,
        },
        "unknown": [
            "all-purpose bit-operation costs of native algebra",
            "factor coefficient growth after a refused/timeout call",
            "peak native allocations (not captured by tracemalloc)",
            "scaling outside finite manually selected r,Q,R and bounded worker budgets",
            "actual paper schedule activation and its full worst-case recurrence",
        ],
    }
    counts: Counter[str] = Counter()
    for f in families:
        for n in sizes:
            for summation in summations:
                rows = []
                for repetition in range(repeats):
                    modes = MODES if repetition % 2 == 0 else tuple(reversed(MODES))
                    for mode in modes:
                        rows.append(_run_worker(
                            f, n, summation, mode, timeout=timeout,
                            threshold=threshold, max_leaves=max_leaves,
                            r=r, Q=Q, R=R, backend=backend,
                            oracle_max_vars=oracle_max_vars,
                        ))
                try:
                    summary = summarize(rows, repeats)
                except ValueError as exc:
                    report["status"] = "failed"
                    report["failed_comparison"] = {
                        "family": f, "nvars": n, "summation": summation,
                        "error": str(exc), "raw_samples": rows,
                    }
                    return report
                report["measurements"].append({"summary": summary, "raw_samples": rows})
                counts[summary["outcome"]] += 1
    report["outcome_counts"] = dict(sorted(counts.items()))
    report["inputs_stable"] = (
        before == fingerprints() and git == git_provenance()
        and natives == native_binaries()
    )
    report["status"] = "complete" if report["inputs_stable"] else "failed_input_drift"
    report["all_cases_solved"] = counts["verified"] == len(families) * len(sizes) * len(summations)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--family", choices=FAMILIES, default="path")
    parser.add_argument("--nvars", type=int, default=2)
    parser.add_argument("--summation", choices=SUMMATIONS, default="eliminate")
    parser.add_argument("--mode", choices=MODES, default="baseline")
    parser.add_argument("--families", nargs="+", default=list(DEFAULT_FAMILIES))
    parser.add_argument("--sizes", nargs="+", type=int, default=list(DEFAULT_SIZES))
    parser.add_argument("--summations", nargs="+", default=list(SUMMATIONS))
    parser.add_argument("--repeats", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=15)
    parser.add_argument("--threshold", type=int, default=64)
    parser.add_argument("--max-leaves", type=int, default=64)
    parser.add_argument("--r", type=int, default=2)
    parser.add_argument("--Q", type=int, default=2)
    parser.add_argument("--R", type=int, default=2)
    parser.add_argument("--backend", choices=("python", "flint"), default="python")
    parser.add_argument("--oracle-max-vars", type=int, default=12)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "artifacts/cnf-scaling.json")
    args = parser.parse_args()
    options = {
        "threshold": args.threshold, "max_leaves": args.max_leaves,
        "r": args.r, "Q": args.Q, "R": args.R, "backend": args.backend,
        "oracle_max_vars": args.oracle_max_vars,
    }
    if args.worker:
        return _worker(args.family, args.nvars, args.summation, args.mode, **options)
    try:
        report = run(
            args.families, args.sizes, args.summations,
            repeats=args.repeats, timeout=args.timeout, **options,
        )
    except Exception as exc:
        report = {"schema_version": SCHEMA, "status": "failed",
                  "error": f"{type(exc).__name__}: {exc}"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"CNF full-pipeline scaling: {report['status']}; {args.output}")
    return 0 if report["status"] == "complete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
