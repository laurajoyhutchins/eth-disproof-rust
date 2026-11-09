#!/usr/bin/env python3
"""Exact, reproducible digit-orbit contraction and independent band oracle.

Run from repository root: PYTHONPATH=src:. python scripts/probe_sudoku_symmetry.py
Neither Ganak nor the brute-force Sudoku solver is called by contraction.
"""
from __future__ import annotations

import json
import sys
from dataclasses import asdict
from itertools import permutations
from pathlib import Path
from time import perf_counter

from non_exponential_sudoku.sudoku.frontier import count_frontier
from non_exponential_sudoku.sudoku.symmetry import OrbitMode, contract_digit_orbits
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.real_sudoku_bench import puzzles


def independent_first_band_count() -> tuple[int, int]:
    """Independent row-permutation oracle with the first row normalized."""
    first = tuple(range(9))
    valid_second = 0
    bands = 0
    for second in permutations(range(9)):
        if any(a == b for a, b in zip(first, second)):
            continue
        if any(set(first[c:c + 3]) & set(second[c:c + 3])
               for c in (0, 3, 6)):
            continue
        valid_second += 1
        thirds = tuple(
            permutations(set(range(9)) - set(first[c:c + 3])
                         - set(second[c:c + 3]))
            for c in (0, 3, 6)
        )
        # Materialize each independent third-row box exactly once.
        parts = tuple(tuple(part) for part in thirds)
        for a in parts[0]:
            for b in parts[1]:
                for c in parts[2]:
                    row = a + b + c
                    if all(row[j] != first[j] and row[j] != second[j]
                           for j in range(9)):
                        bands += 1
    return valid_second, bands


def main() -> None:
    result: dict[str, object] = {
        'python': sys.version,
        'fixture': 'empty 9x9 Sudoku',
        'scope': 'first complete 3-row band, not full Sudoku',
    }
    empty = Puzzle(3, (0,) * 81)
    band_total = 0
    configurations: tuple[tuple[str, OrbitMode, int], ...] = (
        ('pgl_first_row', 'pgl2', 9),
        ('s9_first_row', 'permutations', 9),
        ('s9_first_band', 'permutations', 27),
    )
    for label, mode, cells in configurations:
        started = perf_counter()
        output = contract_digit_orbits(empty, mode=mode, max_cells=cells)
        if label == 's9_first_band':
            band_total = output.partial_assignments
        result[label] = {
            'stats': asdict(output.stats),
            'partial_assignments': output.partial_assignments,
            'solutions': output.solutions,
            'elapsed_seconds': perf_counter() - started,
        }
    started = perf_counter()
    second, normalized_bands = independent_first_band_count()
    result['independent_oracle'] = {
        'second_rows_per_fixed_first': second,
        'complete_bands_per_fixed_first': normalized_bands,
        'all_first_rows': normalized_bands * 362880,
        'elapsed_seconds': perf_counter() - started,
    }
    assert normalized_bands * 362880 == band_total
    name, hard, expected = next(case for case in puzzles()  # type: ignore[no-untyped-call]
                                if case[0] == '9x9-hard-unique')
    base = count_frontier(hard)
    projective = contract_digit_orbits(hard, mode='pgl2')
    full = contract_digit_orbits(hard, mode='permutations')
    suffix = contract_digit_orbits(hard, mode='suffix-permutations')
    assert expected == base.count == projective.solutions == full.solutions == suffix.solutions
    result['hard_puzzle'] = {
        'fixture': name, 'exact_count': expected,
        'baseline_peak_states': base.stats.peak_states,
        'global_s9_peak_orbits': full.stats.peak_orbits,
        'global_pgl_peak_orbits': projective.stats.peak_orbits,
        'suffix_s9_peak_orbits': suffix.stats.peak_orbits,
        'global_s9_stabilizer_order': full.stats.group_order,
        'global_pgl_stabilizer_order': projective.stats.group_order,
    }
    destination = Path('docs/evidence/v031_sudoku/symmetry_probe.json')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
