"""Reproducible tiny #SAT rational-reference probe; not an asymptotic benchmark.

Run: PYTHONPATH=src:. python -m benchmarks.eth.reference_probe --output probe.json
"""
from __future__ import annotations

import argparse
import json
import platform
try:
    import resource
except ImportError:  # Windows has no POSIX resource module.
    resource = None
import time
from fractions import Fraction
from pathlib import Path

from non_exponential_sudoku.eth import (
    CNFFormula, Polynomial, ReplacementForm, ReplacementSystem,
    count_bruteforce, deformation_polynomial,
)


def _peak_rss_bytes() -> int | None:
    # Linux getrusage records KiB, elsewhere the units are not uniform.
    return (resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
            if resource is not None and platform.system() == 'Linux' else None)


def probe(formula: CNFFormula) -> dict[str, object]:
    """Count with two independent exponential references and report exact sizes."""
    # Deterministic non-identity perturbation: x_v + (T/2) x_(v+1).
    replacements = ReplacementSystem(tuple(
        tuple(ReplacementForm(tuple(
            Polynomial((int(index == abs(literal) - 1),
                        Fraction(int(index == abs(literal) % formula.nvars), 2)))
            for index in range(formula.nvars))) for literal in clause)
        for clause in formula.clauses))
    start = time.perf_counter()
    count = count_bruteforce(formula)
    deformation = deformation_polynomial(formula, replacements)
    elapsed = time.perf_counter() - start
    if deformation.at_zero != count:
        raise AssertionError('ETH reference polynomial identity failed')
    return {
        'algorithm_status': 'exhaustive_reference_only',
        'backend': 'python',
        'nvars': formula.nvars,
        'normalized_clauses': len(formula.clauses),
        'count': count,
        'deformation_degree': deformation.degree,
        'boolean_assignments': 1 << formula.nvars,
        'max_coefficient_bits': max(
            max(abs(value.numerator).bit_length(), value.denominator.bit_length())
            for value in deformation.coefficients),
        'peak_process_rss_bytes': _peak_rss_bytes(),
        'wall_seconds': elapsed,
        'capacity_refusal': False,
        'taylor_pairs': None,  # Not implemented by this reference pipeline.
        'measurement_tuples': None,
        'group_assignments': None,
        'estimated_bit_operations': None,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dimacs', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    formula = (CNFFormula.from_dimacs(args.dimacs.read_text()) if args.dimacs
               else CNFFormula(3, ((1, 2), (-1, 3))))
    result = probe(formula)
    payload = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    print(payload, end='')


if __name__ == '__main__':
    main()
