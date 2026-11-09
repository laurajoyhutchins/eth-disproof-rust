"""Reproducible density-to-implicit auxiliary comparison.

Run: PYTHONPATH=src:. python -m benchmarks.eth.implicit_auxiliary_probe

Dense construction is only evaluated where the reference fits.  Larger
examples report actual implicit peak Python allocations plus the virtual
D and D**2 dimensions, not hypothetical dense benchmark timings.
"""
from __future__ import annotations

import json
import statistics
import time
import tracemalloc
from typing import Callable, TypeVar

from non_exponential_sudoku.runtime.budget import CapacityError

from non_exponential_sudoku.eth import (
    CNFFormula, ConstructionLimits, construct_auxiliary,
    construct_implicit_auxiliary, construct_from_schedules,
    count_bruteforce, count_from_constructed, deterministic_schedules,
)

_T = TypeVar('_T')


def _measure(action: Callable[[], _T], *, repeats: int = 3) -> tuple[_T, float, int]:
    times: list[float] = []
    peaks: list[int] = []
    previous: _T | None = None
    for _ in range(repeats):
        tracemalloc.start()
        start = time.perf_counter()
        value = action()
        times.append(time.perf_counter() - start)
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        peaks.append(peak)
        previous = value
    if previous is None:
        raise AssertionError('benchmark produced no result')
    return previous, statistics.median(times), max(peaks)


def probe() -> dict[str, object]:
    cases: list[dict[str, object]] = []
    for Q, R in ((2, 2), (3, 2), (5, 5), (12, 12)):
        D = 4 ** Q
        item: dict[str, object] = {
            'r': 2, 'Q': Q, 'R': R, 'virtual_coordinates': D,
            'virtual_dense_matrix_cells': D * D,
        }
        implicit, elapsed, peak = _measure(
            lambda: construct_implicit_auxiliary(r=2, Q=Q, R=R))
        item.update({
            'implicit_seconds': elapsed,
            'implicit_peak_traced_bytes': peak,
            'exceptional_directions': len(implicit.measurement_selectors),
            'stored_kernel_cells': sum(len(row) for row in implicit.kernel),
        })
        if Q <= 3:
            limits = ConstructionLimits(max_dimension=64, max_auxiliary_cells=4096)
            dense, old_elapsed, old_peak = _measure(
                lambda: construct_auxiliary(r=2, Q=Q, R=R, limits=limits))
            for source in dense.labels:
                for target in dense.labels:
                    assert implicit.row_at(source, target) == dense.rows[
                        implicit.label_index(source)][implicit.label_index(target)]
            item.update({
                'dense_seconds': old_elapsed,
                'dense_peak_traced_bytes': old_peak,
                'speedup': old_elapsed / elapsed if elapsed else None,
            })
        cases.append(item)

    formula = CNFFormula(3, ((1, 2), (-1, 3)))
    a, d = deterministic_schedules(formula, r=2, Q=5)
    aux = construct_implicit_auxiliary(r=2, Q=5, R=5)
    constructed, transfer_seconds, transfer_peak = _measure(
        lambda: construct_from_schedules(formula, aux, a, d), repeats=1)
    assert len(constructed.centers) == 5
    full_counts: list[dict[str, object]] = []
    expected_count = count_bruteforce(formula)
    for Q in (5, 12):
        r = Q
        started = time.perf_counter()
        virtual = construct_implicit_auxiliary(r=2, Q=Q, R=r)
        variables, clauses = deterministic_schedules(formula, r=2, Q=Q)
        design = construct_from_schedules(formula, virtual, variables, clauses)
        preparation_seconds = time.perf_counter() - started
        try:
            answer, count_seconds, count_peak = _measure(
                lambda: count_from_constructed(formula, design), repeats=1)
            if answer != expected_count:
                raise ArithmeticError('implicit large-D count differs from independent #SAT')
            full_counts.append({
                'Q': Q, 'R': r, 'D': virtual.dimension, 'count': answer,
                'preparation_seconds': preparation_seconds,
                'count_seconds': count_seconds, 'count_peak_traced_bytes': count_peak,
                'status': 'exact_count',
            })
        except CapacityError as exc:
            full_counts.append({
                'Q': Q, 'R': r, 'D': virtual.dimension,
                'preparation_seconds': preparation_seconds,
                'status': 'capacity_refusal', 'reason': str(exc),
            })
    return {
        'status': 'exact-auxiliary-component-benchmark-not-ETH-runtime-bound',
        'cases': cases,
        'large_transfer': {
            'Q': 5, 'nvars': formula.nvars,
            'seconds': transfer_seconds, 'peak_traced_bytes': transfer_peak,
            'centers_certified': len(constructed.centers),
        },
        'full_counts': full_counts,
    }


def main() -> None:
    print(json.dumps(probe(), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
