"""Independent partition, conditional-factorization, and resource contracts."""
from __future__ import annotations

from non_exponential_sudoku.sudoku.state import prepare_residual

from itertools import permutations, product
from random import Random

import pytest

from non_exponential_sudoku.sudoku.components import (
    ComponentLimits, _partition, _Work, count_components,
)
from non_exponential_sudoku.sudoku.frontier import (
    FrontierCapacityError, FrontierLimits, count_frontier,
)
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.generalized_bench import canonical_solution
from reference.real_sudoku_bench import puzzles

pytestmark = pytest.mark.checkpoint


def _independent_four_by_four() -> tuple[tuple[int, ...], ...]:
    rows = tuple(permutations(range(1, 5)))
    result = []
    for grid in product(rows, repeat=4):
        board = tuple(value for row in grid for value in row)
        if all({board[r*4+c] for r in range(4)} == {1, 2, 3, 4}
               for c in range(4)) and all(
            {board[r*4+c] for r in range(br, br+2)
             for c in range(bc, bc+2)} == {1, 2, 3, 4}
            for br in (0, 2) for bc in (0, 2)
        ):
            result.append(board)
    return tuple(result)


def _two_rows_erased(block: int) -> tuple[Puzzle, tuple[int, ...]]:
    side = block * block
    solution = tuple(canonical_solution(block))
    return (Puzzle(block, tuple(0 if index // side < 2 else digit
                                for index, digit in enumerate(solution))),
            solution)


def _independent_column_cycles(solution: tuple[int, ...], side: int) -> int:
    """Count legal row-pair completions by disjoint digit cycles, not DP.

    Each column has exactly two missing digits. Selecting which digit goes in
    the first row is equivalent to orienting the edges of a degree-two graph
    whose vertices are digits. All edges in each cycle must have the same
    orientation. The remaining rows and boxes are already complete.
    """
    mapping = {solution[column]: solution[side + column]
               for column in range(side)}
    assert len(mapping) == side
    assert set(mapping) == set(mapping.values())
    seen: set[int] = set()
    cycles = 0
    for digit in mapping:
        if digit in seen:
            continue
        cycles += 1
        current = digit
        while current not in seen:
            seen.add(current)
            current = mapping[current]
    return 1 << cycles


def test_partition_is_certified_by_disjoint_candidate_obligations() -> None:
    puzzle, _ = _two_rows_erased(4)
    choices, valid = prepare_residual(puzzle, None)
    assert valid
    work = _Work(puzzle.side, ComponentLimits())
    groups = _partition(choices, work)
    assert len(groups) == 4
    assert tuple(map(len, groups)) == (8, 8, 8, 8)
    masks = []
    for group in groups:
        union = 0
        for cell in group:
            for choice in choices[cell]:
                union |= choice
        masks.append(union)
    assert all(not masks[i] & masks[j]
               for i in range(len(masks)) for j in range(i+1, len(masks)))


@pytest.mark.parametrize('block', (2, 3, 4, 5, 7, 10))
def test_erased_two_rows_analytic_oracle(block: int) -> None:
    puzzle, original = _two_rows_erased(block)
    expected = _independent_column_cycles(original, puzzle.side)
    output = count_components(puzzle)
    assert expected == 1 << block
    assert output.count == expected
    assert output.stats.initial_components == block
    assert output.stats.largest_initial_component == 2*block
    assert output.stats.peak_states == block
    if block <= 5:
        assert count_frontier(puzzle).count == expected
    if block == 7:
        with pytest.raises(FrontierCapacityError, match='estimated-byte limit'):
            count_frontier(puzzle)


def test_randomized_exact_counts_against_unrelated_four_by_four_enumerator() -> None:
    solutions = _independent_four_by_four()
    assert len(solutions) == 288
    rng = Random(20261108)
    for _ in range(40):
        solved = rng.choice(solutions)
        clues = set(rng.sample(range(16), rng.randrange(0, 14)))
        entries = tuple(solved[pos] if pos in clues else 0 for pos in range(16))
        puzzle = Puzzle(2, entries)
        expected = sum(all(not clue or clue == digit
                           for clue, digit in zip(entries, candidate))
                       for candidate in solutions)
        assert count_components(puzzle).count == expected
        assert count_components(puzzle, mode='adaptive').count == expected
        # Explicit arbitrary domains count a *different* constrained problem.
        domains = tuple((1 << (value-1)) if value else
                        15 ^ (1 << rng.randrange(4)) for value in entries)
        restricted = sum(all(domains[cell] & (1 << (digit - 1))
                             for cell, digit in enumerate(candidate))
                         for candidate in solutions)
        assert count_components(puzzle, domains=domains).count == restricted
        assert count_components(puzzle, mode='adaptive', domains=domains).count == restricted


def test_adaptive_conditional_independence_and_negative_control() -> None:
    empty = Puzzle(2, (0,) * 16)
    static = count_components(empty, mode='static')
    adaptive = count_components(empty, mode='adaptive')
    assert static.count == adaptive.count == 288
    assert static.stats.initial_components == adaptive.stats.initial_components == 1
    assert adaptive.stats.conditional_splits > 0
    _, hard, _ = next(item for item in puzzles() if item[0] == '9x9-hard-unique')
    reference = count_frontier(hard)
    original = count_components(hard)
    conditioned = count_components(hard, mode='adaptive')
    assert reference.count == original.count == conditioned.count == 1
    assert original.stats.peak_states == reference.stats.peak_states == 1261
    assert conditioned.stats.initial_components == 1
    # Conditional decomposition does not improve every graph.
    assert conditioned.stats.peak_states > original.stats.peak_states


def test_refusal_limits_input_validation_and_unsatisfiable_board() -> None:
    puzzle = Puzzle(2, (0,) * 16)
    for mode in ('static', 'adaptive'):
        with pytest.raises(FrontierCapacityError, match='state limit'):
            count_components(puzzle, mode=mode, limits=ComponentLimits(
                frontier=FrontierLimits(max_states=1)))
        with pytest.raises(FrontierCapacityError, match='transition limit'):
            count_components(puzzle, mode=mode, limits=ComponentLimits(
                frontier=FrontierLimits(max_transitions=1)))
        with pytest.raises(FrontierCapacityError, match='estimated-byte limit'):
            count_components(puzzle, mode=mode, limits=ComponentLimits(
                frontier=FrontierLimits(max_estimated_bytes=1)))
        with pytest.raises(FrontierCapacityError, match='graph-visit limit'):
            count_components(puzzle, mode=mode, limits=ComponentLimits(
                max_graph_visits=1))
    with pytest.raises(FrontierCapacityError, match='recursion depth limit'):
        count_components(puzzle, mode='adaptive', limits=ComponentLimits(
            max_recursive_cells=1))
    with pytest.raises(ValueError, match='positive'):
        ComponentLimits(max_graph_visits=0)
    with pytest.raises(ValueError, match='Unknown component counting mode'):
        count_components(puzzle, mode='bogus')  # type: ignore[arg-type]
    with pytest.raises(ValueError, match='Incorrect domain vector length'):
        count_components(puzzle, domains=(15,))
    with pytest.raises(ValueError, match='Invalid domain'):
        count_components(puzzle, domains=(16,)+(15,)*15)
    with pytest.raises(ValueError, match='Domain contradicts given'):
        count_components(Puzzle(2, (1,)+(0,)*15), domains=(2,)+(15,)*15)
    assert count_components(Puzzle(2, (1, 1)+(0,)*14)).count == 0
    assert count_components(Puzzle(1, (0,))).count == 1
    assert count_components(Puzzle(1, (1,)), mode='adaptive').count == 1
