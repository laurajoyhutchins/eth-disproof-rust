"""Repeatable exact-arithmetic microbenchmarks and small constructed-count check.

Run: PYTHONPATH=src:. python -m benchmarks.eth.algebraic_readout --output readout.json

This is a *component* benchmark.  Spectral Q=7 does not fit the existing
dense auxiliary constructor, and readout timings exclude generating the
rational Taylor data.  End-to-end count timings are separately identified.
"""
from __future__ import annotations

import argparse
import json
import statistics
import time
import tracemalloc
from fractions import Fraction
from pathlib import Path

from non_exponential_sudoku.eth import (
    CNFFormula, Polynomial, construct_bounded_designs,
    count_bruteforce, count_from_constructed,
)
from non_exponential_sudoku.eth.construction import (
    _interpolation_polynomial, _walsh_coefficients,
)
from non_exponential_sudoku.eth.interpolation import (
    HermiteDatum, interpolate_hermite, interpolate_origin_hermite,
)
from non_exponential_sudoku.eth.modular_readout import interpolate_integer_origin_crt


def _measure(fn: object, repeats: int) -> tuple[object, float, int]:
    if not callable(fn):
        raise TypeError('benchmark target must be callable')
    seconds = []
    peaks = []
    answer: object = None
    for _ in range(repeats):
        tracemalloc.start()
        start = time.perf_counter()
        value = fn()
        seconds.append(time.perf_counter() - start)
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        peaks.append(peak)
        if answer is not None and value != answer:
            raise ArithmeticError('nondeterministic benchmark result')
        answer = value
    return answer, statistics.median(seconds), max(peaks)


def _cube_walsh(polynomial: Polynomial, Q: int) -> dict[int, Fraction]:
    values: dict[int, Fraction] = {}
    for mask in range(1 << Q):
        coefficient = sum(
            (polynomial.evaluate(subset.bit_count()) *
             (-1 if (mask & subset).bit_count() % 2 else 1)
             for subset in range(1 << Q)), Fraction(0),
        ) / (1 << Q)
        if coefficient:
            values[mask] = coefficient
    return values


def probe(*, repeats: int = 3) -> dict[str, object]:
    if repeats < 1:
        raise ValueError('repeats must be positive')
    polynomial = _interpolation_polynomial((1, 2, 3, 4))
    spectral_reference, sr_seconds, sr_peak = _measure(
        lambda: _cube_walsh(polynomial, 7), repeats)
    spectral_new, sn_seconds, sn_peak = _measure(
        lambda: _walsh_coefficients(polynomial, 7), repeats)
    if spectral_reference != spectral_new:
        raise ArithmeticError('compressed spectral mismatch')

    coefficients = [Fraction(123_456_789)]
    coefficients.extend(Fraction((-1) ** i * ((1 << 255) + i * 31), 2 * i + 3)
                        for i in range(1, 36))
    target = Polynomial(tuple(coefficients))
    data = []
    for center in range(1, 7):
        coeff = target.taylor(center, 5).coefficients
        data.append(HermiteDatum(Fraction(center), coeff +
                                 (Fraction(0),) * (6 - len(coeff))))
    rational, r_seconds, r_peak = _measure(
        lambda: interpolate_hermite(data, degree_bound=35).polynomial.at_zero,
        repeats)
    origin, o_seconds, o_peak = _measure(
        lambda: interpolate_origin_hermite(data, degree_bound=35).value,
        repeats)
    crt, c_seconds, c_peak = _measure(
        lambda: interpolate_integer_origin_crt(
            data, max_value=1 << 32, moduli=(2_147_483_647, 2_147_483_629)),
        repeats)
    if not rational == origin == crt == target.at_zero:
        raise ArithmeticError('Hermite readout mismatch')

    formula = CNFFormula(3, ((1, -2), (-1, 3), (2, 3)))
    design = construct_bounded_designs(formula, r=2, Q=2, R=2)
    count_poly, p_seconds, _ = _measure(
        lambda: count_from_constructed(formula, design, readout='polynomial'),
        repeats)
    count_origin, n_seconds, _ = _measure(
        lambda: count_from_constructed(formula, design, readout='origin'),
        repeats)
    if not count_poly == count_origin == count_bruteforce(formula):
        raise ArithmeticError('constructed #SAT mismatch')

    return {
        'status': 'exact-component-benchmark; not a worst-case speedup claim',
        'repeats': repeats,
        'spectral': {
            'Q': 7, 'R': 4, 'nonzero_coefficients': len(spectral_new),
            'cube_seconds': sr_seconds, 'compressed_seconds': sn_seconds,
            'cube_peak_traced_bytes': sr_peak, 'compressed_peak_traced_bytes': sn_peak,
        },
        'hermite': {
            'degree': 35, 'centers': 6, 'taylor_coefficients_per_center': 6,
            'rational_seconds': r_seconds, 'origin_seconds': o_seconds,
            'crt_seconds': c_seconds,
            'rational_peak_traced_bytes': r_peak,
            'origin_peak_traced_bytes': o_peak,
            'crt_peak_traced_bytes': c_peak,
        },
        'constructed_count': {
            'variables': formula.nvars, 'count': count_origin,
            'polynomial_seconds': p_seconds, 'origin_seconds': n_seconds,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = probe(repeats=args.repeats)
    serialized = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized)
    print(serialized, end='')


if __name__ == '__main__':
    main()
