"""Independent #SAT oracle comparison; never used by the production counter."""
from __future__ import annotations

import pytest

from non_exponential_sudoku.eth.ganak import count_ganak
from non_exponential_sudoku.eth.sudoku_adapter import from_sudoku_puzzle
from non_exponential_sudoku.sudoku.frontier import count_frontier
from reference.real_sudoku_bench import puzzles

pytestmark = pytest.mark.integration


def test_hard_sudoku_matches_real_ganak() -> None:
    pytest.importorskip('pyganak')
    puzzle = next(p for name, p, _ in puzzles() if name == '9x9-hard-unique')
    actual = count_frontier(puzzle)
    reference = count_ganak(from_sudoku_puzzle(puzzle))
    assert actual.count == reference == 1
