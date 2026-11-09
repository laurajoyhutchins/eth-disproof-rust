"""Pinned same-runner before/after benchmark; fresh worker per observation."""
from __future__ import annotations
import argparse
from dataclasses import asdict
from fractions import Fraction
import gc
import json
import os
from pathlib import Path
import platform
import resource
import statistics
import subprocess
import sys
import tempfile
from time import perf_counter_ns
import tracemalloc

HERE = Path(__file__).resolve()
ROOT = HERE.parents[1]
BEFORE = "89308831b7304b66fe969cdee6e2ada989fc5636"
AFTER = "a9072cad2614d934bbed868d875fef55600829f5"
PAIRED = ("local-9x9", "recursive-parity-2wire", "recursive-sudoku-4wire",
          "recursive-nested-2wire", "frontier-hard", "frontier-hall")
OPTIONAL = ("frontier-hard-matching", "frontier-hall-matching")


def exercise(case: str, kind: str) -> tuple[int, dict]:
    if case == "local-9x9":
        from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
        from non_exponential_sudoku.sudoku.direct_network import DirectNetwork
        from non_exponential_sudoku.sudoku.encoding import sudoku_network
        from non_exponential_sudoku.sudoku.three_cnf import Puzzle
        puzzle = Puzzle(3, (0,) * 81)
        t = perf_counter_ns()
        reference = DirectNetwork.from_puzzle(puzzle)
        net = sudoku_network(puzzle)
        setup_ms = (perf_counter_ns() - t) / 1e6
        solution = tuple((r * 3 + r // 3 + c) % 9 + 1
                         for r in range(9) for c in range(9))
        assert puzzle.valid_solution(solution)
        witness = reference.witness_edges(solution)
        samples = []
        for vertex in net.left + net.right:
            good = tuple(witness[e] for e in vertex.ports)
            samples.extend(((vertex, good), (vertex, (0,) * len(good)),
                            (vertex, (1,) * len(good)),
                            (vertex, (1 - good[0],) + good[1:])))
        ring = Padic(5, modulus_polynomial(5), 5)
        iterations = 160 if kind == "timing" else 40
        good_count = 0
        t = perf_counter_ns()
        for _ in range(iterations):
            for vertex, bits in samples:
                good_count += int(vertex.oracle(bits, ring) != ring.zero)
        return good_count, {"oracle_calls": iterations * len(samples),
                            "wire_count": reference.edge_count,
                            "setup_ms": round(setup_ms, 4),
                            "evaluation_ms": round((perf_counter_ns() - t)/1e6, 4)}

    if case.startswith("recursive-"):
        from benchmarks.recursive_cases import get_case
        from non_exponential_sudoku.contraction import engine as em
        from non_exponential_sudoku.contraction import deformation as dm
        benchmark = get_case(case.removeprefix("recursive-"), "plans")
        counts = {"mode_catalog_calls": 0, "factor_plan_builds": 0}
        catalog, factor_plan = em.mode_catalog, dm.build_factorization_plan
        def counted_catalog(*args, **kwargs):
            counts["mode_catalog_calls"] += 1
            return catalog(*args, **kwargs)
        def counted_plan(*args, **kwargs):
            counts["factor_plan_builds"] += 1
            return factor_plan(*args, **kwargs)
        em.mode_catalog = counted_catalog
        dm.build_factorization_plan = counted_plan
        try:
            engine = em.ContractionEngine(benchmark.config)
            answer = int(engine.contract(benchmark.network)[0])
            assert answer == benchmark.expected
            stats = asdict(engine.stats)
        finally:
            em.mode_catalog, dm.build_factorization_plan = catalog, factor_plan
        keys = ("recursive_calls", "child_networks", "leaves",
                "interpolation_evaluations", "compiled_child_plans",
                "mode_dp_operations", "mode_dp_local_child_evaluations")
        return answer, {**counts, **{key: int(stats[key]) for key in keys}}

    if case.startswith("frontier-"):
        from non_exponential_sudoku.sudoku.frontier import count_frontier
        from non_exponential_sudoku.sudoku.three_cnf import Puzzle
        from reference.real_sudoku_bench import puzzles
        if "hard" in case:
            puzzle = next(p for name, p, _ in puzzles()
                          if name == "9x9-hard-unique")
        else:
            puzzle = Puzzle(2, (1,0,3,0,3,0,0,0,0,0,0,0,0,0,0,0))
        if case.endswith("-matching"):
            answer = count_frontier(puzzle, projection="matching")
        else:
            answer = count_frontier(puzzle)
        stats = asdict(answer.stats)
        keys = ("free_cells", "candidate_choices", "peak_states",
                "transitions", "compatible_transitions", "max_frontier_bits")
        return int(answer.count), {key: int(stats[key]) for key in keys}
    raise ValueError(case)


def worker(case: str, kind: str) -> None:
    if kind == "memory":
        gc.collect()
        tracemalloc.start()
    t = perf_counter_ns()
    answer, operations = exercise(case, kind)
    elapsed = (perf_counter_ns() - t) / 1e6
    trace_kib = None
    if kind == "memory":
        trace_kib = tracemalloc.get_traced_memory()[1] / 1024
        tracemalloc.stop()
    print(json.dumps({"case": case, "kind": kind, "answer": answer,
                      "elapsed_ms": elapsed,
                      "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                      "traced_peak_kib": trace_kib, "operations": operations},
                     sort_keys=True))


def observe(worktree: Path, case: str, kind: str) -> dict:
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join((str(worktree / "src"), str(worktree)))
    env.update(PYTHONHASHSEED="0", OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1")
    result = subprocess.run(
        [sys.executable, str(HERE), "--worker", "--case", case, "--kind", kind],
        cwd=worktree, env=env, text=True, capture_output=True, timeout=90)
    if result.returncode:
        raise RuntimeError(f"{case}/{kind}/{worktree.name}: "
                           f"{result.returncode}: {result.stdout[-1000:]} {result.stderr[-4000:]}")
    return json.loads(result.stdout.strip().splitlines()[-1])


def median(samples: list[dict], key: str) -> float:
    return round(float(statistics.median(x[key] for x in samples)), 4)


def compare(raw: dict) -> dict:
    summary = {}
    for case in PAIRED:
        b, a = raw["before"][case], raw["after"][case]
        if case == "local-9x9":
            # Memory workers intentionally use fewer loops. Compare normalized
            # nonzero tensor outcomes per oracle call, not raw totals.
            signatures = {
                Fraction(row["answer"], row["operations"]["oracle_calls"])
                for group in (b, a) for records in group.values() for row in records
            }
            if len(signatures) != 1:
                raise AssertionError(f"Local tensor checksum mismatch: {signatures}")
            answer = b["timing"][0]["answer"]
        else:
            counts = {row["answer"] for group in (b, a)
                      for records in group.values() for row in records}
            if len(counts) != 1:
                raise AssertionError(f"Exact-count mismatch for {case}: {counts}")
            answer = next(iter(counts))
        before_ms = median(b["timing"], "elapsed_ms")
        after_ms = median(a["timing"], "elapsed_ms")
        summary[case] = {
            "answer": answer, "before_ms": before_ms, "after_ms": after_ms,
            "speedup": round(before_ms / after_ms, 4),
            "before_rss_kib": median(b["memory"], "peak_rss_kib"),
            "after_rss_kib": median(a["memory"], "peak_rss_kib"),
            "before_traced_kib": median(b["memory"], "traced_peak_kib"),
            "after_traced_kib": median(a["memory"], "traced_peak_kib"),
            "before_ops": b["timing"][0]["operations"],
            "after_ops": a["timing"][0]["operations"],
        }
        for side, group in (("before", b), ("after", a)):
            if any(row["operations"] != group["timing"][0]["operations"]
                   for row in group["timing"] if case != "local-9x9"):
                raise AssertionError(f"Non-deterministic counters: {case}/{side}")
    for case in OPTIONAL:
        matching, default = raw["after"][case], raw["after"][case.removesuffix("-matching")]
        counts = {row["answer"] for group in (matching, default)
                  for records in group.values() for row in records}
        if len(counts) != 1:
            raise AssertionError(f"Optional matching changed count for {case}")
        summary[case] = {
            "answer": next(iter(counts)), "after_only": True,
            "default_ms": median(default["timing"], "elapsed_ms"),
            "matching_ms": median(matching["timing"], "elapsed_ms"),
            "default_rss_kib": median(default["memory"], "peak_rss_kib"),
            "matching_rss_kib": median(matching["memory"], "peak_rss_kib"),
            "default_ops": default["timing"][0]["operations"],
            "matching_ops": matching["timing"][0]["operations"],
        }
    return summary


def main(args: argparse.Namespace) -> None:
    with tempfile.TemporaryDirectory(prefix="shift-left-comparison-") as folder:
        base = Path(folder)
        revisions = {"before": (args.before, base / "before"),
                     "after": (args.after, base / "after")}
        for sha, path in revisions.values():
            subprocess.run(["git", "worktree", "add", "--detach", str(path), sha],
                           cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
        raw = {"before": {}, "after": {}}
        for case in (*PAIRED, *OPTIONAL):
            participants = ("after",) if case in OPTIONAL else ("before", "after")
            for side in participants:
                raw[side][case] = {"timing": [], "memory": []}
            for kind, repeats in (("timing", args.rounds), ("memory", args.memory_rounds)):
                for index in range(repeats):
                    ordered = participants if index % 2 == 0 else participants[::-1]
                    for side in ordered:
                        sample = observe(revisions[side][1], case, kind)
                        raw[side][case][kind].append(sample)
                        print(f"SAMPLE {case} {side} {kind} #{index}: "
                              f"{sample['elapsed_ms']:.3f}ms answer={sample['answer']}",
                              flush=True)
        summary = compare(raw)
        environment = {"python": sys.version, "platform": platform.platform(),
                       "timing_samples": args.rounds,
                       "memory_samples": args.memory_rounds,
                       "fresh_process_per_sample": True,
                       "timing_and_memory_runs_separate": True,
                       "rss_unit": "KiB (Linux RUSAGE_SELF peak)",
                       "local_oracle_timing_iterations": 160,
                       "local_oracle_memory_iterations": 40,
                       "cpu_model": next((line.split(":", 1)[1].strip()
                           for line in Path("/proc/cpuinfo").read_text().splitlines()
                           if line.startswith("model name")), None)}
        document = {"schema": "nonexp-sudoku.shift-left.v1",
                    "before": args.before, "after": args.after,
                    "environment": environment, "summary": summary, "samples": raw}
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
        for case, row in summary.items():
            print("RESULT " + json.dumps({"case": case, **row}, sort_keys=True), flush=True)
        print(f"REPORT {args.output}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--case", default="")
    parser.add_argument("--kind", choices=("timing", "memory"), default="timing")
    parser.add_argument("--before", default=BEFORE)
    parser.add_argument("--after", default=AFTER)
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--memory-rounds", type=int, default=2)
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts" / "shift-left.json")
    opts = parser.parse_args()
    if opts.worker:
        worker(opts.case, opts.kind)
    else:
        if opts.rounds < 1 or opts.memory_rounds < 1:
            parser.error("sample counts must be positive")
        main(opts)
