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
from itertools import product
from statistics import median
from time import perf_counter_ns

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.contraction.children import make_child
from non_exponential_sudoku.contraction.packets import EvaluationContext, PacketEntry
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.sudoku.encoding import port_graph_with_cross_mode
from reference.packet_oracle_work import packet_evaluation_envelope
from reference.target_coefficient import (
    ExtractionStats, LinearRow,
    expanded_coefficient_reference, target_coefficient_by_components,
    evaluate_packet_target_coefficient,
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


def verify_actual_packet_fixture() -> dict[str, str | int | bool]:
    """Independent real prepared packet entries, not arbitrary affine rows."""
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    ring = Padic(5, modulus_polynomial(5), 9)
    modes = mode_catalog(net, packing, 1, ring.p)
    evaluated = 0
    nonzero_targets = 0
    largest_target_modes = 0
    max_reference_state_capacity = 0
    max_pruned_peak_states = 0
    for beta in ((0,) * len(modes), (1,) * len(modes)):
        context = EvaluationContext(1, ring.one, ring, 1)
        for group in (0, 1):
            child = make_child(net, packing, modes, beta, 1, ring.one, ring,
                               group, 0, context)
            for vertex in child.right:
                entry = vertex.oracle
                if not isinstance(entry, PacketEntry):
                    raise TypeError("child did not contain a prepared packet entry")
                largest_target_modes = max(largest_target_modes, len(entry.terms.desired))
                nonzero_targets += bool(entry.terms.desired)
                bound = packet_evaluation_envelope(entry)
                max_reference_state_capacity = max(
                    max_reference_state_capacity, bound.coefficient_states
                )
                for bits in product((0, 1), repeat=len(vertex.ports)):
                    baseline = entry._evaluate_python(bits)
                    stats = ExtractionStats()
                    experimental = evaluate_packet_target_coefficient(entry, bits, stats=stats)
                    if baseline != experimental:
                        raise AssertionError("real packet entry coefficient mismatch")
                    evaluated += 1
                    max_pruned_peak_states = max(max_pruned_peak_states, stats.peak_states)
    return {
        "family": "real_prepared_cross_mode_packet",
        "evaluations": evaluated,
        "nonzero_target_packet_entries": nonzero_targets,
        "largest_target_modes": largest_target_modes,
        "unpruned_state_capacity_bound_not_measured": max_reference_state_capacity,
        "pruned_peak_states_observed": max_pruned_peak_states,
        "all_exact_results_equal": True,
    }


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args(argv)
    print(json.dumps({
        "scope": "synthetic sparse affine factors over exact Padic; not actual paper Sudoku",
        "timing": "same-process observational medians, not production performance",
        "cases": run(args.repeats),
        "real_packet": verify_actual_packet_fixture(),
    }, indent=2))


if __name__ == "__main__":
    main()
