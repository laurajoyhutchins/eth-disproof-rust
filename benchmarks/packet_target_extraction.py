"""Reproducible source-level coefficient-state experiment, not a Sudoku speedup.

Run: PYTHONPATH=src:. python -m benchmarks.packet_target_extraction

The compared algorithms share one eager finite ring and preconstructed
affine factors. Timings INCLUDE Python interpreter and dictionary overhead
and are not isolated-process timing claims. Deterministic state counts are
the primary evidence; no CI assertion relies on benchmark speed.
"""
from __future__ import annotations

import argparse
import json
from collections.abc import Sequence
from statistics import median
from time import perf_counter_ns

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from reference.target_coefficient import (
    ExtractionStats, LinearRow,
    expanded_coefficient_reference, target_coefficient_by_components,
)


def _cases(ring: Padic) -> list[tuple[str, int, tuple[LinearRow, ...]]]:
    one = ring.one
    zero = ring.zero
    cases: list[tuple[str, int, tuple[LinearRow, ...]]] = []
    for n in (6, 9, 12):
        cases.append((
            "independent", n,
            tuple(LinearRow(one, ((i, one),)) for i in range(n)),
        ))
        cases.append((
            "connected_cycle", n,
            tuple(LinearRow(zero, ((i, one), ((i+1) % n, one)))
                  for i in range(n)),
        ))
    for n in (6, 9, 12):
        cases.append((
            "size_3_components", n,
            tuple(LinearRow(zero, tuple((3*j+k, one) for k in range(3)))
                  for j in range(n//3) for _ in range(3)),
        ))
    for n in (4, 6, 8):
        cases.append((
            "dense_permanent", n,
            tuple(LinearRow(zero, tuple((j, one) for j in range(n)))
                  for _ in range(n)),
        ))
    return cases


def run(repeats: int = 3) -> list[dict[str, int | float | str | bool]]:
    if repeats < 1:
        raise ValueError("repeats must be positive")
    ring = Padic(3, modulus_polynomial(3), 19)
    records: list[dict[str, int | float | str | bool]] = []
    for family, n, factors in _cases(ring):
        target = (1,) * n
        baseline_stats, reduced_stats = ExtractionStats(), ExtractionStats()
        baseline = expanded_coefficient_reference(
            ring, factors, target, stats=baseline_stats,
        )
        reduced = target_coefficient_by_components(
            ring, factors, target, stats=reduced_stats,
        )
        if baseline != reduced:
            raise AssertionError(f"coefficient mismatch in {family}/{n}")
        ordinary_times: list[int] = []
        reduced_times: list[int] = []
        for _ in range(repeats):
            before = perf_counter_ns()
            a = expanded_coefficient_reference(ring, factors, target)
            ordinary_times.append(perf_counter_ns() - before)
            before = perf_counter_ns()
            b = target_coefficient_by_components(ring, factors, target)
            reduced_times.append(perf_counter_ns() - before)
            if a != b:
                raise AssertionError("benchmark repetition changed exact result")
        records.append({
            "family": family,
            "modes": n,
            "same_exact_coefficient": True,
            "independent_components": reduced_stats.components,
            "largest_component_modes": reduced_stats.largest_component_modes,
            "baseline_peak_states": baseline_stats.peak_states,
            "pruned_peak_states": reduced_stats.peak_states,
            "baseline_transitions": baseline_stats.retained_transitions,
            "pruned_transitions": reduced_stats.retained_transitions,
            "rejected_unreachable_transitions": reduced_stats.pruned_transitions,
            "baseline_median_ns": int(median(ordinary_times)),
            "pruned_median_ns": int(median(reduced_times)),
        })
    return records


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args(argv)
    print(json.dumps({
        "scope": "synthetic sparse affine factors over exact Padic; not actual paper Sudoku",
        "timing": "same-process observational medians, not production performance",
        "cases": run(args.repeats),
    }, indent=2))


if __name__ == "__main__":
    main()
