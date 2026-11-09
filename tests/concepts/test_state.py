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


def test_candidate_restrictions_change_the_problem_not_the_counter() -> None:
    from non_exponential_sudoku.sudoku.frontier import count_frontier

    puzzle = Puzzle(2, (0,) * 16)
    unrestricted = count_frontier(puzzle)
    domains = (1,) + ((1 << 4) - 1,) * 15
    restricted = count_frontier(puzzle, domains=domains)
    assert unrestricted.count == 288
    assert restricted.count == 72
    choices, admissible = prepare_residual(puzzle, domains)
    assert admissible
    assert len(choices) == 15
