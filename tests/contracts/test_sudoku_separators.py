"""Exact separator conditioning and oblivious boundary-ordering contracts."""
from __future__ import annotations

from itertools import permutations, product
from random import Random

import pytest

from non_exponential_sudoku.sudoku.components import count_components
from non_exponential_sudoku.sudoku.frontier import (
    FrontierCapacityError, FrontierLimits, count_frontier,
)
from non_exponential_sudoku.sudoku.separators import (
    StructuralLimits, count_structural,
)
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.generalized_bench import canonical_solution
from reference.real_sudoku_bench import puzzles

pytestmark = pytest.mark.checkpoint

# A deliberately restricted *empty* 4x4. The choices are not inferred from
# givens and therefore count a different, explicitly restricted problem.
# All nine remaining nonfixed cells have at least two legal candidates. Cell
# 11 is a genuine articulation vertex separating groups of four cells.
CONNECTED_DOMAINS = (
    1, 15, 4, 15, 4, 10, 1, 14, 14, 4, 11, 15, 11, 1, 14, 4,
)


def _independent_four_by_four() -> tuple[tuple[int, ...], ...]:
    rows = tuple(permutations(range(1, 5)))
    return tuple(board for grid in product(rows, repeat=4)
                 if (board := tuple(x for row in grid for x in row))
                 and all({board[r*4+c] for r in range(4)} == {1, 2, 3, 4}
                         for c in range(4))
                 and all({board[r*4+c] for r in range(br, br+2)
                          for c in range(bc, bc+2)} == {1, 2, 3, 4}
                         for br in (0, 2) for bc in (0, 2)))


def test_proven_separator_on_connected_nontrivial_restricted_problem() -> None:
    puzzle = Puzzle(2, (0,) * 16)
    reference = sum(all(mask & (1 << (value-1))
                        for mask, value in zip(CONNECTED_DOMAINS, board))
                    for board in _independent_four_by_four())
    assert reference == 4
    direct = count_frontier(puzzle, domains=CONNECTED_DOMAINS)
    conditioned = count_structural(
        puzzle, domains=CONNECTED_DOMAINS, method='condition')
    automatic = count_structural(puzzle, domains=CONNECTED_DOMAINS,
                                 method='auto')
    assert direct.count == conditioned.count == automatic.count == reference
    assert conditioned.stats.conflict_edges == 13
    assert conditioned.stats.initial_components == 1
    assert conditioned.stats.chosen_separator == (11,)
    assert conditioned.stats.resulting_component_sizes == (4, 4)
    assert conditioned.stats.considered_separator_assignments == 3
    assert conditioned.stats.compatible_separator_assignments == 3
    assert conditioned.stats.smallest_separator_size == 1
    assert conditioned.stats.separator_search_complete
    assert automatic.stats.method_used == 'condition'


def test_hard_nine_by_nine_is_width_not_small_separators() -> None:
    _, puzzle, expected = next(item for item in puzzles()
                               if item[0] == '9x9-hard-unique')
    original = count_frontier(puzzle)
    boundary = count_structural(puzzle, method='boundary')
    audited = count_structural(puzzle, method='auto')
    assert original.count == boundary.count == audited.count == expected == 1
    assert original.stats.peak_states == 1261
    assert boundary.stats.peak_states == 330
    assert boundary.stats.transitions == 28349
    assert boundary.stats.peak_states < 500
    assert boundary.stats.transitions < original.stats.transitions
    assert audited.stats.method_used == 'boundary'
    assert audited.stats.conflict_edges == 387
    assert audited.stats.initial_components == 1
    assert audited.stats.separator_search_complete
    assert audited.stats.smallest_separator_size is None
    assert audited.stats.separator_probes == 58 + 58*57//2
    with pytest.raises(FrontierCapacityError, match='No eligible separator'):
        count_structural(puzzle, method='condition')


def test_independent_two_row_family_preserves_product_without_conditioning() -> None:
    for b in (2, 3, 4, 5, 7, 10):
        side = b*b
        solved = tuple(canonical_solution(b))
        puzzle = Puzzle(b, tuple(0 if index // side < 2 else x
                                 for index, x in enumerate(solved)))
        output = count_structural(puzzle)
        assert output.count == 1 << b
        assert output.stats.initial_components == b
        assert output.stats.chosen_separator == ()
        assert output.stats.method_used == 'independent-components'
        assert output.stats.peak_states <= b


def test_randomized_four_by_four_against_independent_enumerator() -> None:
    solutions = _independent_four_by_four()
    assert len(solutions) == 288
    rng = Random(20261108)
    for _ in range(36):
        solved = rng.choice(solutions)
        clues = set(rng.sample(range(16), rng.randrange(0, 14)))
        entries = tuple(solved[i] if i in clues else 0 for i in range(16))
        puzzle = Puzzle(2, entries)
        expected = sum(all(x == 0 or x == y for x, y in zip(entries, board))
                       for board in solutions)
        for method in ('boundary', 'auto'):
            assert count_structural(puzzle, method=method).count == expected
        domains = tuple(1 << (x-1) if x else 15 ^ (1 << rng.randrange(4))
                        for x in entries)
        restricted = sum(all(mask & (1 << (y-1))
                             for mask, y in zip(domains, board))
                         for board in solutions)
        assert count_structural(puzzle, domains=domains).count == restricted
        assert count_components(puzzle, domains=domains).count == restricted


def test_refusals_and_incomplete_search_do_not_claim_negative_certificates() -> None:
    empty = Puzzle(2, (0,) * 16)
    with pytest.raises(FrontierCapacityError, match='state limit'):
        count_structural(empty, limits=StructuralLimits(frontier=FrontierLimits(
            max_states=1)))
    with pytest.raises(FrontierCapacityError, match='transition limit'):
        count_structural(empty, limits=StructuralLimits(frontier=FrontierLimits(
            max_transitions=1)))
    with pytest.raises(FrontierCapacityError, match='estimated-byte limit'):
        count_structural(empty, limits=StructuralLimits(frontier=FrontierLimits(
            max_estimated_bytes=1)))
    with pytest.raises(FrontierCapacityError, match='Component graph-visit limit'):
        count_structural(empty, limits=StructuralLimits(max_graph_visits=1))
    with pytest.raises(FrontierCapacityError, match='ordering evaluation limit'):
        count_structural(empty, limits=StructuralLimits(max_order_evaluations=1))
    with pytest.raises(ValueError, match='Invalid structural'):
        StructuralLimits(max_separator_probes=0)
    with pytest.raises(ValueError, match='Unknown structural counting method'):
        count_structural(empty, method='oops')  # type: ignore[arg-type]
    with pytest.raises(FrontierCapacityError, match='No eligible separator'):
        count_structural(empty, method='condition',
                         limits=StructuralLimits(max_separator_cells=0))
    controlled = count_structural(
        Puzzle(2, (0,) * 16), domains=CONNECTED_DOMAINS,
        method='auto', limits=StructuralLimits(max_separator_probes=1))
    assert controlled.count == 4
    assert not controlled.stats.separator_search_complete
    assert controlled.stats.separator_probes == 1
    assert controlled.stats.smallest_separator_size is None
    assert controlled.stats.method_used == 'boundary'
    assert count_structural(Puzzle(2, (1, 1) + (0,)*14)).count == 0
    assert count_structural(Puzzle(1, (1,))).count == 1
