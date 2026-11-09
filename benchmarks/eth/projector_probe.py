"""Exact exceptional-projector vs explicit selector performance probe.

Reproduce: PYTHONPATH=src:. python -m benchmarks.eth.projector_probe

The global exceptional projector has the correct row space, but reduction
can yield up to one independent row per occupied variable, so results do
NOT certify the paper's small-tau measurement bound.  The larger Q=48,
R=8 case exercises Q>=6R but is not the literal paper n-derived schedule.
"""
from __future__ import annotations

import json
import time
import tracemalloc
from fractions import Fraction

from non_exponential_sudoku.eth import (
    CNFFormula, ConstructionLimits, construct_from_schedules,
    count_bruteforce, count_from_constructed, deterministic_schedules,
)
from non_exponential_sudoku.eth.construction import construct_implicit_auxiliary


def _case(Q: int, R: int, *, count: bool) -> dict[str, object]:
    formula = CNFFormula(3, ((1, 2), (-1, 3)))
    limits = ConstructionLimits(max_implicit_points=64, max_measurement_rows=128)
    tracemalloc.start()
    start = time.perf_counter()
    aux = construct_implicit_auxiliary(
        r=2, Q=Q, R=R, limits=limits, measurement_basis='projector')
    build_seconds = time.perf_counter() - start
    _, build_peak = tracemalloc.get_traced_memory()
    schedules = deterministic_schedules(formula, r=2, Q=Q)
    transfer_start = time.perf_counter()
    construction = construct_from_schedules(
        formula, aux, *schedules, limits=limits)
    transfer_seconds = time.perf_counter() - transfer_start
    _, transfer_peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    max_row_l1 = max((sum(abs(v) for v in row)
                      for _, design in construction.centers
                      for matrix in design.matrices for row in matrix), default=0)
    result: dict[str, object] = {
        'Q': Q, 'R': R, 'D': aux.dimension,
        'virtual_matrix_cells': aux.dimension**2,
        'global_exceptional_basis_count': aux.exceptional_count,
        'exceptional_fraction': str(Fraction(aux.exceptional_count, aux.dimension)),
        'retained_exceptional_selectors': len(aux.measurement_selectors),
        'actual_max_measurements': construction.max_measurement_rows,
        'max_row_l1': max_row_l1,
        'build_seconds': build_seconds,
        'transfer_seconds': transfer_seconds,
        'build_peak_traced_bytes': build_peak,
        'transfer_peak_traced_bytes': transfer_peak,
        'centers_certified': len(construction.centers),
    }
    if count:
        readout_start = time.perf_counter()
        answer = count_from_constructed(formula, construction)
        count_seconds = time.perf_counter() - readout_start
        expected = count_bruteforce(formula)
        if answer != expected:
            raise AssertionError('projected count disagrees with independent #SAT oracle')
        result['count'] = answer
        result['count_seconds'] = count_seconds
    return result


def probe() -> dict[str, object]:
    return {
        'status': 'measured-exact-projection-not-ETH-worst-case-bound',
        'cases': [_case(2, 2, count=True), _case(12, 2, count=True),
                  _case(48, 8, count=True)],
    }


def main() -> None:
    print(json.dumps(probe(), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
