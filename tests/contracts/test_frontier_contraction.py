"""Independent exact-count and refusal contracts for Sudoku frontier DP."""
from __future__ import annotations

from itertools import permutations, product
from random import Random

import pytest

from non_exponential_sudoku.sudoku.frontier import (
    FrontierCapacityError,
    FrontierLimits,
    count_frontier,
)
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.generalized_bench import canonical_solution
from reference.local_support import pin_band_wires, projected_domains
from reference.real_sudoku_bench import independent_count_sparse, puzzles

# Each contract has exactly one verification tier. Expensive reference cases
# run in integration; small exact and refusal contracts remain checkpoint.


def _all_solutions_four_by_four() -> tuple[tuple[int, ...], ...]:
    """Independent test oracle, enumerating valid row permutations only."""
    rows = tuple(permutations(range(1, 5)))
    solutions = []
    for board_rows in product(rows, repeat=4):
        board = tuple(x for row in board_rows for x in row)
        if all(set(board[r * 4 + c] for r in range(4)) == {1, 2, 3, 4}
               for c in range(4)) and all(
            set(board[r * 4 + c] for r in range(br, br + 2)
                for c in range(bc, bc + 2)) == {1, 2, 3, 4}
            for br in (0, 2) for bc in (0, 2)
        ):
            solutions.append(board)
    return tuple(solutions)


@pytest.mark.parametrize('name', (
    '4x4-12-givens-two-solutions',
    '4x4-8-givens-four-solutions',
    '9x9-77-givens-two-solutions',
    '9x9-73-givens-four-solutions',
    '9x9-easy-unique',
    '9x9-hard-unique',
    '9x9-contradictory-clues',
    '16x16-252-givens-two-solutions',
))
@pytest.mark.checkpoint
def test_canonical_counts_without_fallback(name: str) -> None:
    _, puzzle, expected = next(c for c in puzzles() if c[0] == name)
    result = count_frontier(puzzle)
    assert result.count == expected
    assert result.stats.peak_states <= 100_000
    assert result.stats.compatible_transitions <= result.stats.transitions
    if expected:
        assert result.stats.peak_live_states >= result.stats.peak_states


@pytest.mark.checkpoint
def test_hard_177_wire_failure_is_bounded_exact_contraction() -> None:
    _, puzzle, _ = next(c for c in puzzles() if c[0] == '9x9-hard-unique')
    _, residual = pin_band_wires(puzzle)
    assert residual['remaining_wires'] == 177
    result = count_frontier(puzzle, limits=FrontierLimits(
        max_states=2_000,
        max_transitions=100_000,
        max_estimated_bytes=2 * 1024 * 1024,
    ))
    assert result.count == 1
    assert result.stats.peak_states == 1261
    assert result.stats.free_cells == 58
    assert result.stats.max_frontier_bits <= 81
    assert result.stats.merged_transitions > 0
    # Independently computed polynomial-time all-different GAC, not a witness.
    projected, _ = projected_domains(puzzle)
    projected_result = count_frontier(puzzle, domains=projected)
    assert projected_result.count == result.count
    assert projected_result.stats.free_cells == 57


@pytest.mark.checkpoint
def test_empty_four_by_four_and_random_clues() -> None:
    solutions = _all_solutions_four_by_four()
    assert len(solutions) == 288
    assert count_frontier(Puzzle(2, (0,) * 16)).count == len(solutions)
    rng = Random(20261108)
    seed = canonical_solution(2)
    for _ in range(48):
        keep = set(rng.sample(range(16), rng.randrange(2, 14)))
        entries = tuple(value if pos in keep else 0
                        for pos, value in enumerate(seed))
        puzzle = Puzzle(2, entries)
        expected = sum(all(not clue or clue == value
                           for clue, value in zip(entries, solution))
                       for solution in solutions)
        assert count_frontier(puzzle).count == expected
        assert count_frontier(puzzle, order='minimum-domain').count == expected


@pytest.mark.checkpoint
def test_small_independent_digit_enumerator() -> None:
    for name, puzzle, expected in puzzles():
        independent = independent_count_sparse(puzzle, 8)
        if independent is None:
            continue
        assert independent == expected, name
        assert count_frontier(puzzle).count == independent, name


@pytest.mark.checkpoint
def test_projection_restrictions_are_explicit() -> None:
    puzzle = Puzzle(2, (0,) * 16)
    domains = [15] * 16
    domains[0] = 1
    reduced = count_frontier(puzzle, domains=domains)
    assert reduced.count == 72  # digit symmetry of the unlabelled 4x4 board
    with pytest.raises(ValueError, match='Domain vector'):
        count_frontier(puzzle, domains=(1,))
    with pytest.raises(ValueError, match='Invalid candidate'):
        count_frontier(puzzle, domains=(0,) + (15,) * 15)
    with pytest.raises(ValueError, match='Invalid candidate'):
        count_frontier(puzzle, domains=(16,) + (15,) * 15)
    given = Puzzle(2, (1,) + (0,) * 15)
    with pytest.raises(ValueError, match='contradicts given'):
        count_frontier(given, domains=(2,) + (15,) * 15)
    with pytest.raises(ValueError, match='ordering'):
        count_frontier(puzzle, order='random')  # type: ignore[arg-type]


@pytest.mark.checkpoint
def test_all_resource_limits_refuse_without_fallback() -> None:
    _, puzzle, _ = next(c for c in puzzles() if c[0] == '9x9-hard-unique')
    with pytest.raises(FrontierCapacityError, match='state limit'):
        count_frontier(puzzle, limits=FrontierLimits(max_states=10))
    with pytest.raises(FrontierCapacityError, match='transition limit'):
        count_frontier(puzzle, limits=FrontierLimits(max_transitions=10))
    with pytest.raises(FrontierCapacityError, match='estimated-byte limit'):
        count_frontier(puzzle, limits=FrontierLimits(max_estimated_bytes=512))
    with pytest.raises(FrontierCapacityError, match='state limit'):
        count_frontier(Puzzle(3, (0,) * 81),
                       limits=FrontierLimits(max_states=1000))
    with pytest.raises(ValueError, match='positive'):
        FrontierLimits(max_states=0)


@pytest.mark.integration
def test_pure_function_determinism_and_traversal_order() -> None:
    _, puzzle, _ = next(c for c in puzzles() if c[0] == '9x9-hard-unique')
    a = count_frontier(puzzle)
    b = count_frontier(puzzle)
    assert a == b
    # The alternative ordering computes the same exact sum but uses much
    # more frontier states.  It is intentionally checked under a larger cap.
    c = count_frontier(puzzle, order='minimum-domain', limits=FrontierLimits(
        max_states=400_000,
        max_transitions=12_000_000,
        max_estimated_bytes=256 * 1024 * 1024,
    ))
    assert c.count == a.count == 1
    assert c.stats.peak_states > 100 * a.stats.peak_states
