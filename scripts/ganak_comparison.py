#!/usr/bin/env python3
"""Reproducible independent #SAT checks against Ganak and Sudoku 3-CNF.

This is *not* a runtime comparison with the research contraction engine.
The Ganak binding is a trusted independent implementation under test; small
random instances are cross-checked against exhaustive enumeration and Sudoku
instances against known exact completion counts.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
import random
import statistics
import sys
import time
from importlib.metadata import version
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT))

from non_exponential_sudoku.sudoku.three_cnf import CNF, Puzzle
from research.ganak_oracle import count_cnf
from scripts.evidence import fingerprints, git_provenance


def exhaustive(formula: CNF) -> int:
    if formula.nvars > 16:
        raise ValueError("Refusing exponential enumeration above 16 variables")
    return sum(formula.satisfied([False, *assignment])
               for assignment in product((False, True), repeat=formula.nvars))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "benchmark-results/ganak-oracle.json")
    parser.add_argument("--seed", type=int, default=87111)
    parser.add_argument("--random-instances", type=int, default=30)
    args = parser.parse_args()
    if args.random_instances < 0:
        parser.error("--random-instances must be nonnegative")
    rng = random.Random(args.seed)
    result: list[dict[str, int | str | bool]] = []
    timings: list[int] = []

    def record(label: str, formula: CNF, expected: int) -> None:
        before = time.perf_counter_ns()
        observed = count_cnf(formula, seed=args.seed)
        elapsed = time.perf_counter_ns() - before
        timings.append(elapsed)
        if observed != expected:
            raise AssertionError(f"{label}: Ganak returned {observed}, expected {expected}")
        result.append({"case": label, "nvars": formula.nvars,
                       "clauses": len(formula.clauses), "count": observed,
                       "wall_ns": elapsed, "matched_reference": True})

    for i in range(args.random_instances):
        nvars = rng.randint(1, 8)
        clauses = [tuple(rng.choice((-1, 1)) * rng.randint(1, nvars)
                         for _ in range(rng.randint(1, 3)))
                   for _ in range(rng.randint(0, 10))]
        f = CNF(nvars=nvars, clauses=clauses)
        record(f"random-{i}", f, exhaustive(f))

    for name, puzzle, box, exact_count in [
        ("single-cell", ".", 1, 1),
        ("solved-four-by-four", "1234341221434321", 2, 1),
        ("contradictory-four-by-four", "11" + "." * 14, 2, 0),
        ("empty-four-by-four", "." * 16, 2, 288),
    ]:
        record(name, Puzzle.from_text(puzzle, box).encode(), exact_count)

    report = {
        "schema_version": "1.0.0",
        "status": "verified",
        "scope": "exact nonprojected #SAT of declared CNF variables",
        "exclusions": ["weighted counts", "projected counts", "general solver speed comparisons"],
        "environment": {"python": sys.version.split()[0], "platform": platform.platform(),
                        "pyganak": version("pyganak"), "git": git_provenance(),
                        "fingerprints": fingerprints(),
                        "adapter_sha256": hashlib.sha256((ROOT / "research/ganak_oracle.py").read_bytes()).hexdigest()},
        "parameters": {"seed": args.seed, "random_instances": args.random_instances},
        "cases": result,
        "median_wall_ns": int(statistics.median(timings)),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    print(f"Verified {len(result)} exact #SAT instances: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
