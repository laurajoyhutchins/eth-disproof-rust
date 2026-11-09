"""Reproducible, fail-closed memory experiment in fresh Linux processes.

One worker prepares one independently checkable exact workload, starts
tracemalloc, measures exactly one operation and exits. The driver aggregates
repeated workers, never treating a refusal or missing record as a measurement.

Peak RSS is a whole-process high-water mark. Python-traced allocations omit
untracked native buffers. Neither observation is a guarantee about future
resource use or proof that an estimator is conservative.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, replace
from itertools import product
from math import comb, isfinite
import importlib.util
import json
import os
from pathlib import Path
import platform
import resource
import subprocess
import sys
import time
import tracemalloc
from collections.abc import Callable, Mapping
from typing import Any

from non_exponential_sudoku import CachePolicy
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.network import compile_leaf_plan, eliminate_leaf, simple_network

CASES = (
    "leaf.lookup", "leaf.indexed", "mode.grid3",
    "nested.jet", "recursive.nested", "recursive.nested.cap64k",
)
SCHEMA = "1.0.0"


@dataclass(frozen=True)
class MemorySample:
    case_id: str
    status: str
    expected: int
    actual: int | None
    elapsed_seconds: float
    description: str
    memory: dict[str, int]
    solver_estimates: dict[str, int]
    process_id: int

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, raw: Mapping[str, Any]) -> MemorySample:
        if not isinstance(raw, Mapping):
            raise ValueError("Invalid memory record")
        try:
            return cls(
                case_id=raw["case_id"], status=raw["status"],
                expected=raw["expected"], actual=raw["actual"],
                elapsed_seconds=raw["elapsed_seconds"],
                description=raw["description"],
                memory=dict(raw["memory"]),
                solver_estimates=dict(raw["solver_estimates"]),
                process_id=raw["process_id"],
            )
        except (KeyError, TypeError, ValueError) as exc:
            raise ValueError("Incomplete memory record") from exc


def validate_sample(sample: MemorySample, *, case_id: str) -> None:
    if (sample.case_id != case_id or sample.status != "verified"
            or type(sample.expected) is not int or sample.expected < 1
            or type(sample.actual) is not int or sample.actual != sample.expected
            or not isinstance(sample.description, str) or not sample.description
            or type(sample.process_id) is not int or sample.process_id <= 0
            or type(sample.elapsed_seconds) not in (int, float)
            or not isfinite(sample.elapsed_seconds) or sample.elapsed_seconds < 0):
        raise ValueError("Incorrect, refused or incomplete exact-memory sample")
    fields = (
        "rss_before_bytes", "rss_after_bytes", "rss_high_water_bytes",
        "rss_high_water_growth_bytes",
        "python_tracemalloc_baseline_bytes", "python_tracemalloc_end_bytes",
        "python_tracemalloc_peak_bytes", "python_tracemalloc_peak_growth_bytes",
    )
    if any(key not in sample.memory or type(sample.memory[key]) is not int
           or sample.memory[key] < 0 for key in fields):
        raise ValueError("Invalid or missing byte measurement")
    rss = sample.memory
    if (rss["rss_high_water_bytes"] < max(rss["rss_before_bytes"], rss["rss_after_bytes"])
            or rss["rss_high_water_growth_bytes"] != max(
                0, rss["rss_high_water_bytes"] - rss["rss_before_bytes"])
            or rss["python_tracemalloc_peak_bytes"] < max(
                rss["python_tracemalloc_end_bytes"],
                rss["python_tracemalloc_baseline_bytes"])
            or rss["python_tracemalloc_peak_growth_bytes"] != max(
                0, rss["python_tracemalloc_peak_bytes"]
                - rss["python_tracemalloc_baseline_bytes"])):
        raise ValueError("Inconsistent peak-memory measurements")
    if any(not isinstance(name, str) or type(value) is not int or value < 0
           for name, value in sample.solver_estimates.items()):
        raise ValueError("Invalid solver accounting")


def _process_rss() -> int:
    """Linux /proc observed resident set, as opposed to process peak."""
    for line in Path("/proc/self/status").read_text().splitlines():
        if line.startswith("VmRSS:"):
            return int(line.split()[1]) * 1024
    raise RuntimeError("Linux VmRSS is required for comparable observations")


def prepare_case(
    case_id: str,
) -> tuple[Callable[[], int], int, str, Callable[[], dict[str, int]]]:
    """Prepare fixtures *outside* the measured operation."""
    if case_id in ("leaf.lookup", "leaf.indexed"):
        all_four = {bits: 1 for bits in product((0, 1), repeat=4)}
        all_two = {bits: 1 for bits in product((0, 1), repeat=2)}
        net = simple_network(
            8, [((0, 1, 2, 3), all_four), ((4, 5, 6, 7), all_four)],
            [((i, i + 4), all_two) for i in range(4)],
        )
        ring = Padic(5, modulus_polynomial(5), 17)
        expected = 1 << net.edges
        if net.direct(ring, net.edges)[0] != expected:
            raise AssertionError("Independent exhaustive leaf reference disagrees")
        budget = 8192 if case_id == "leaf.lookup" else 0
        scopes = tuple(v.ports for v in net.left + net.right)
        plan = compile_leaf_plan(net.edges, scopes, max_width=8,
                                 lookup_budget=budget)
        if plan is None:
            raise AssertionError("Expected valid compiled leaf order")
        if case_id == "leaf.indexed" and any(s.lookup is not None for s in plan.steps):
            raise AssertionError("Indexed leaf should never precompute lookups")
        def run_leaf() -> int:
            return int(eliminate_leaf(net, ring, 8, 8, plan=plan,
                                      max_factor_bytes=16 * 1024 * 1024)[0])
        return run_leaf, expected, (
            "8-wire exact Boolean leaf; compiled lookup" if budget
            else "8-wire exact Boolean leaf; indexed lookup"
        ), lambda: {"leaf_max_factor_bytes": 16 * 1024 * 1024,
                    "leaf_compiled_lookup_entries": budget}

    if case_id == "mode.grid3":
        # Existing independently checked GF(2)-style sparse grid workload.
        from benchmarks.growth_worker import case
        stats, run, expected, _ = case("grid-sparse", 3)
        return run, expected, "Sparse 3x3 exact mode-DP grid", lambda: {
            "mode_dp_peak_estimated_bytes": stats.mode_dp_peak_estimated_bytes,
            "mode_dp_peak_factor_states": stats.mode_dp_peak_factor_states,
            "mode_dp_peak_polynomial_terms": stats.mode_dp_peak_polynomial_terms,
        }

    if case_id == "nested.jet":
        base = Padic(5, modulus_polynomial(5), 25)
        inner = JetRing(base, 8)
        outer = JetRing(inner, 12)
        operand = outer.add(outer.one, outer.variable)
        # Independent coefficient formula for (1+z)^n modulo z**12.
        n_last = 43
        expected_coeffs = tuple(inner.scalar(comb(n_last, k))
                                for k in range(outer.q))
        expected = sum(comb(n_last, k) & base.mask for k in range(outer.q))
        def run_nested() -> int:
            value = outer.one
            for n in range(32, n_last + 1):
                value = outer.pow(operand, n)
            if value != expected_coeffs:
                raise AssertionError("Nested jets differ from independent binomial coefficients")
            return sum(value[k][0][0] for k in range(outer.q))
        return run_nested, expected, (
            "Two-level 2-adic exact Taylor arithmetic against binomial oracle"
        ), lambda: {"nested_scalar_coordinates_per_coefficient":
                    base.e * inner.q * outer.q}

    if case_id in ("recursive.nested", "recursive.nested.cap64k"):
        from benchmarks.recursive_cases import get_case
        from non_exponential_sudoku import ContractionEngine
        case = get_case("nested-2wire", "plans")
        config = case.config
        if case_id.endswith("cap64k"):
            config = replace(
                config, recursion=replace(config.recursion, shared_cache_bytes=65536,
                                          child_cache=CachePolicy(8 * 1024 * 1024, 128),
                                          compiled_plans=CachePolicy(8 * 1024 * 1024, 64)),
            )
        engine = ContractionEngine(config)
        return (
            lambda: int(engine.contract(case.network)[0]), case.expected,
            "Two-active-level recursive contraction, " +
            ("shared 64KiB cache budget" if case_id.endswith("cap64k")
             else "independent cache budgets"),
            lambda: {
                "shared_cache_peak_estimated_bytes":
                    engine.stats.shared_cache_peak_estimated_bytes,
                "child_cache_peak_estimated_bytes":
                    engine.stats.child_cache_peak_estimated_bytes,
                "child_plan_cache_peak_estimated_bytes":
                    engine.stats.child_plan_cache_peak_estimated_bytes,
                "mode_dp_peak_estimated_bytes":
                    engine.stats.mode_dp_peak_estimated_bytes,
                "prepared_packet_peak_estimated_bytes":
                    engine.stats.prepared_packet_peak_estimated_bytes,
                "packet_entry_memo_peak_estimated_bytes":
                    engine.stats.packet_entry_memo_peak_estimated_bytes,
            },
        )
    raise ValueError(f"Unknown memory study case: {case_id}")


def sample_once(case_id: str) -> MemorySample:
    run, expected, description, estimates = prepare_case(case_id)
    before = _process_rss()
    # One-frame tracing reduces instrumentation overhead; Python-only.
    tracemalloc.start(1)
    try:
        baseline, _ = tracemalloc.get_traced_memory()
        tracemalloc.reset_peak()
        start = time.perf_counter()
        actual = run()
        elapsed = time.perf_counter() - start
        current, peak = tracemalloc.get_traced_memory()
        after = _process_rss()
        high_water = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
    finally:
        tracemalloc.stop()
    sample = MemorySample(
        case_id=case_id, status="verified" if actual == expected else "incorrect",
        expected=expected, actual=actual, elapsed_seconds=elapsed,
        description=description,
        memory={
            "rss_before_bytes": before,
            "rss_after_bytes": after,
            "rss_high_water_bytes": high_water,
            "rss_high_water_growth_bytes": max(0, high_water - before),
            "python_tracemalloc_baseline_bytes": baseline,
            "python_tracemalloc_end_bytes": current,
            "python_tracemalloc_peak_bytes": peak,
            "python_tracemalloc_peak_growth_bytes": max(0, peak - baseline),
        },
        solver_estimates=estimates(), process_id=os.getpid(),
    )
    validate_sample(sample, case_id=case_id)
    return sample


def aggregate_samples(
    samples: Mapping[str, list[MemorySample]], *, required: tuple[str, ...] = CASES,
) -> dict[str, Any]:
    if set(samples) != set(required):
        raise ValueError("Missing, duplicated or unexpected memory study case")
    sizes = {len(value) for value in samples.values()}
    if len(sizes) != 1 or not sizes or next(iter(sizes)) < 1:
        raise ValueError("Incomplete memory study repetitions")
    for case_id in required:
        for observation in samples[case_id]:
            validate_sample(observation, case_id=case_id)
    return {
        "schema_version": SCHEMA, "status": "verified",
        "instrumentation": {
            "rss": "Linux RUSAGE_SELF high-water KiB converted to bytes",
            "rss_baseline": "/proc/self/status VmRSS prior to tracemalloc",
            "traced_peak": "tracemalloc Python-tracked bytes since reset_peak; excludes native untracked buffers",
            "source": "one fresh worker process per case per repeat",
            "memory_estimates": "Algorithm-specific structural accounting, not measured process RSS",
        },
        "environment": {
            "python": sys.version.split()[0], "platform": platform.platform(),
            "native_ring_available": importlib.util.find_spec("native_ring") is not None,
            "git_commit": _git_head(),
        },
        "cases": [
            {"case_id": case_id,
             "samples": [s.to_dict() for s in samples[case_id]],
             "sample_count": len(samples[case_id])}
            for case_id in required
        ],
    }


def _git_head() -> str | None:
    result = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True,
                            text=True, timeout=5, check=False)
    return result.stdout.strip() if result.returncode == 0 else None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", action="store_true",
                        help="One exact operation, one JSON record, one process")
    parser.add_argument("--case", choices=CASES)
    parser.add_argument("--cases", nargs="+", choices=CASES, default=list(CASES))
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=45)
    parser.add_argument("--output", type=Path, default=Path("artifacts/memory-study.json"))
    args = parser.parse_args()
    if args.worker:
        if args.case is None:
            parser.error("--worker requires --case")
        try:
            print(json.dumps(sample_once(args.case).to_dict(), sort_keys=True))
            return 0
        except Exception as exc:
            print(json.dumps({"case_id": args.case, "status": "failed",
                              "error": f"{type(exc).__name__}: {exc}"},
                             sort_keys=True))
            return 1
    if args.repeats < 1 or not isfinite(args.timeout) or args.timeout <= 0:
        parser.error("repeats and timeout must be positive")
    requested = tuple(args.cases)
    if len(set(requested)) != len(requested):
        parser.error("Case IDs must not repeat")
    observations: dict[str, list[MemorySample]] = {case: [] for case in requested}
    try:
        for case_id in requested:
            for _ in range(args.repeats):
                result = subprocess.run(
                    [sys.executable, "-m", "benchmarks.memory_study",
                     "--worker", "--case", case_id],
                    capture_output=True, text=True, timeout=args.timeout,
                    check=False,
                )
                if result.returncode or len(result.stdout.splitlines()) != 1:
                    raise RuntimeError(
                        f"Incomplete worker for {case_id}: returncode={result.returncode}; "
                        f"stdout={result.stdout[-500:]!r}; stderr={result.stderr[-500:]!r}"
                    )
                sample = MemorySample.from_dict(json.loads(result.stdout))
                validate_sample(sample, case_id=case_id)
                observations[case_id].append(sample)
        report = aggregate_samples(observations, required=requested)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        print(f"Verified {len(requested)} cases x {args.repeats} isolated runs: {args.output}")
        return 0
    except (RuntimeError, ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print(f"Memory study incomplete: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
