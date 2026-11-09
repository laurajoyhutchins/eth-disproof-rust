"""Reproducible exact Taylor factorization benchmark for sparse group chains.

Run: PYTHONPATH=src:. python -m benchmarks.eth.factorized_taylor_probe

The paper's measurement-tuple reference enumerates (2D+1)**m values.
The factorized contraction instead sums group Boolean masks by induced
factor scope.  This demonstrates a finite-size alternative for sparse
group interaction, not a general subexponential #SAT worst-case bound.
"""
from __future__ import annotations

import json
import time
import tracemalloc
from fractions import Fraction

from non_exponential_sudoku.eth import CNFFormula, MeasurementDesign
from non_exponential_sudoku.eth.interpolation import count_origin_from_manual_designs
from non_exponential_sudoku.eth.taylor import TaylorLimits


def _fibonacci(number: int) -> int:
    a, b = 0, 1
    for _ in range(number):
        a, b = b, a + b
    return a


def _chain(n: int) -> tuple[CNFFormula, MeasurementDesign]:
    if n % 2 or n < 4:
        raise ValueError('chain requires an even variable count >= 4')
    groups = tuple((i, i + 1) for i in range(0, n, 2))
    formula = CNFFormula(n, tuple((2 * i + 1, 2 * i + 3)
                                  for i in range(n // 2 - 1)))
    design = MeasurementDesign(
        groups=groups,
        clause_groups=tuple(range(len(formula.clauses))),
        matrices=tuple(((1, 0), (0, 1)) for _ in groups),
        tau=Fraction(1, 2), D=1,
    )
    return formula, design


def _case(n: int) -> dict[str, object]:
    formula, design = _chain(n)
    expected = _fibonacci(n // 2 + 2) * (1 << (n // 2))
    if expected <= 0:
        raise AssertionError('invalid reference count')
    tracemalloc.start()
    started = time.perf_counter()
    computed = count_origin_from_manual_designs(
        formula, ((Fraction(1), design),), order=0,
        summation='eliminate',
        taylor_limits=TaylorLimits(max_measurement_tuples=1, max_factor_entries=128),
    )
    elapsed = time.perf_counter() - started
    _, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    if computed.count != expected:
        raise ArithmeticError('factorized chain differs from Fibonacci oracle')
    stats = computed.taylor_data[0].stats
    entry: dict[str, object] = {
        'variables': n,
        'groups': n // 2,
        'clauses': len(formula.clauses),
        'measurement_rows': n,
        'unvisited_measurement_tuples': 3 ** n,
        'count': computed.count,
        'factorized_seconds': elapsed,
        'factorized_peak_traced_bytes': peak,
        'factor_assignments_tested': stats.factor_assignments_tested,
        'factor_scope_peak': stats.factor_scope_peak,
        'factor_entries_peak': stats.factor_entries_peak,
        'factor_eliminations': stats.factor_eliminations,
        'max_coefficient_bits': stats.max_coefficient_bits,
    }
    if n <= 8:
        tracemalloc.start()
        started = time.perf_counter()
        reference = count_origin_from_manual_designs(
            formula, ((Fraction(1), design),), order=0,
            summation='tuples')
        reference_seconds = time.perf_counter() - started
        _, reference_peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        if reference.count != expected:
            raise ArithmeticError('tuple reference differs from exact count')
        entry['tuple_reference_seconds'] = reference_seconds
        entry['tuple_reference_peak_traced_bytes'] = reference_peak
    return entry


def probe() -> dict[str, object]:
    return {
        'status': 'finite-size exact group-factor contraction, not worst-case ETH bound',
        'cases': [_case(n) for n in (4, 8, 12, 20, 32, 64)],
    }


def main() -> None:
    print(json.dumps(probe(), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
