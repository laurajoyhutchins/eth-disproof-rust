"""Every solver sees the same candidate-obligation representation."""
import pytest
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from non_exponential_sudoku.sudoku.state import (
    candidate_bits, initial_domains, prepare_residual,
)

pytestmark = pytest.mark.checkpoint


def test_three_obligations_and_distinct_row_column_box_positions() -> None:
    n = 4
    for c in range(n * n):
        for d in range(n):
            bits = candidate_bits(c, d, n, 2)
            assert bits.bit_count() == 3
            assert bits.bit_length() <= 3 * n * n


def test_conflicting_givens_yield_empty_residual() -> None:
    p = Puzzle(2, (1, 1) + (0,) * 14)
    assert initial_domains(p) is None
    assert prepare_residual(p, None) == ({}, False)


def test_domains_are_an_explicit_restriction() -> None:
    p = Puzzle(2, (1,) + (0,) * 15)
    domains = initial_domains(p)
    assert domains is not None
    assert domains[0] == 1
    narrowed = tuple(mask & -mask for mask in domains)
    choices, possible = prepare_residual(p, narrowed)
    assert isinstance(choices, dict)
    assert isinstance(possible, bool)
