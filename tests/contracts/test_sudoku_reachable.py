"""Measured reachable-frontier ordering with independent exact-count oracles."""
from __future__ import annotations

from random import Random

import pytest

from non_exponential_sudoku.sudoku.frontier import FrontierCapacityError, FrontierLimits
from non_exponential_sudoku.sudoku.separators import (
    StructuralLimits, count_structural,
)
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.generalized_bench import canonical_solution
from reference.mrv_count import count_mrv_reference
from reference.real_sudoku_bench import puzzles

# Each contract has exactly one verification tier. Expensive reference cases
# run in integration; small exact and refusal contracts remain checkpoint.


def _random_deletion(block: int, clues: int, seed: int) -> Puzzle:
    solved = canonical_solution(block)
    retained = set(Random(seed).sample(range(len(solved)), clues))
    return Puzzle(block, tuple(value if index in retained else 0
                               for index, value in enumerate(solved)))


@pytest.mark.checkpoint
def test_hard_nine_by_nine_reachable_order_preserves_exact_count() -> None:
    puzzle = next(p for name, p, _ in puzzles() if name == '9x9-hard-unique')
    reference = count_structural(puzzle, method='boundary')
    reachable = count_structural(puzzle, method='reachable')
    assert reference.count == reachable.count == 1
    assert reference.stats.peak_states == 330
    assert reachable.stats.peak_states == 268
    assert reachable.stats.transitions == 16584
    assert reachable.stats.pilot_transitions > reachable.stats.transitions
    assert reachable.stats.pilot_evaluations > 0
    assert reachable.stats.method_used == 'reachable'
    assert reachable.stats.separator_probes == 0


@pytest.mark.integration
def test_connected_sixteen_by_sixteen_survives_boundary_refusal() -> None:
    puzzle = _random_deletion(4, 120, 1)
    independent, visited = count_mrv_reference(puzzle)
    assert independent == 177
    assert visited == 25811
    with pytest.raises(FrontierCapacityError, match='state limit'):
        count_structural(puzzle, method='boundary')
    reachable = count_structural(puzzle, method='reachable')
    assert reachable.count == independent
    assert reachable.stats.free_cells >= 100
    assert reachable.stats.initial_components == 1
    assert reachable.stats.peak_states == 3592
    assert reachable.stats.transitions == 374744
    assert reachable.stats.pilot_transitions == 299187
    assert reachable.stats.pilot_evaluations > 0


@pytest.mark.checkpoint
def test_reachable_is_exact_on_random_small_puzzles() -> None:
    rng = Random(20261109)
    for _ in range(28):
        clues = rng.randrange(0, 14)
        puzzle = _random_deletion(2, clues, rng.randrange(100000))
        independent, _ = count_mrv_reference(puzzle)
        reachable = count_structural(puzzle, method='reachable')
        boundary = count_structural(puzzle, method='boundary')
        assert reachable.count == boundary.count == independent
    empty = Puzzle(2, (0,) * 16)
    assert count_structural(empty, method='reachable').count == 288
    assert count_structural(Puzzle(2, (1, 1) + (0,)*14),
                            method='reachable').count == 0


@pytest.mark.checkpoint
def test_reachability_budgets_refuse_explicitly() -> None:
    hard = next(p for name, p, _ in puzzles() if name == '9x9-hard-unique')
    with pytest.raises(FrontierCapacityError, match='pilot transition limit'):
        count_structural(hard, method='reachable', limits=StructuralLimits(
            max_pilot_transitions=1))
    with pytest.raises(FrontierCapacityError, match='ordering evaluation limit'):
        count_structural(hard, method='reachable', limits=StructuralLimits(
            max_order_evaluations=1))
    with pytest.raises(FrontierCapacityError, match='state limit'):
        count_structural(hard, method='reachable', limits=StructuralLimits(
            frontier=FrontierLimits(max_states=1)))
    for overrides in ({'pilot_sample_states': 0},
                      {'pilot_candidate_cells': 0},
                      {'max_pilot_transitions': 0}):
        with pytest.raises(ValueError, match='Invalid structural'):
            StructuralLimits(**overrides)
