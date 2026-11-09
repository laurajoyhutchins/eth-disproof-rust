"""Independent whole-band check of exact Sudoku digit-orbit contraction."""
from __future__ import annotations

import pytest

from non_exponential_sudoku.sudoku.symmetry import contract_digit_orbits
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from scripts.probe_sudoku_symmetry import independent_first_band_count

pytestmark = pytest.mark.integration


def test_empty_nine_by_nine_first_band_independently() -> None:
    second_rows, bands_per_fixed_first = independent_first_band_count()
    assert (second_rows, bands_per_fixed_first) == (12096, 2612736)
    quotient = contract_digit_orbits(Puzzle(3, (0,) * 81), max_cells=27)
    assert quotient.solutions is None  # 54 cells remain, not a Sudoku count.
    assert quotient.partial_assignments == bands_per_fixed_first * 362880
    assert quotient.partial_assignments == 948109639680
    assert quotient.stats.peak_orbits == 95112
    assert quotient.stats.final_orbits == 22620
