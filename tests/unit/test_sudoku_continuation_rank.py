"""Exact continuation (Hankel flattening) rank and symmetry witnesses.

Tests use independently enumerated valid Sudoku grids, never the
production frontier count as the source of their ranks.
"""
from __future__ import annotations

from collections import defaultdict
from math import factorial

import pytest

from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.sudoku_continuation_rank import (
    blank_four_by_four_cut,
    completed_four_by_four_grids,
    exact_first_row_rank,
    prefix_signature,
)

pytestmark = pytest.mark.checkpoint


def test_four_by_four_independent_solution_oracle() -> None:
    puzzle = Puzzle(2, (0,) * 16)
    solutions = completed_four_by_four_grids()
    assert len(solutions) == 288
    assert len(set(solutions)) == 288
    assert all(puzzle.valid_solution(solution) for solution in solutions)


@pytest.mark.parametrize(
    "cut,expected_rank,orbit_sizes,structural_bits", [
        (0, 1, (1,), 0),
        (4, 24, (24,), 24),
        (7, 72, (12, 12, 24, 24), 24),
        (8, 36, (6, 6, 24), 16),
        (16, 1, (1,), 0),
    ],
)
def test_hankel_identity_minor_and_digit_orbits(
    cut: int, expected_rank: int,
    orbit_sizes: tuple[int, ...], structural_bits: int,
) -> None:
    audit = blank_four_by_four_cut(cut)
    assert audit.solutions == 288
    assert audit.cut == cut
    assert audit.extendable_signatures == audit.exact_flattening_rank == expected_rank
    assert audit.structural_frontier_bits == structural_bits
    assert audit.identity_minor_verified
    assert audit.orbit_sizes == orbit_sizes
    assert audit.digit_orbits == len(orbit_sizes)
    assert sum(orbit_sizes) == expected_rank


def test_prefixes_with_equal_signature_have_identical_suffix_acceptance() -> None:
    # This tests the other half of the theorem: an identity minor gives
    # rank >= extendable states, while equality of all same-signature
    # residual functions gives rank <= extendable states.
    puzzle = Puzzle(2, (0,) * 16)
    solutions = completed_four_by_four_grids()
    cut = 8
    grouped: dict[int, list[tuple[int, ...]]] = defaultdict(list)
    for solution in solutions:
        grouped[prefix_signature(puzzle, solution, tuple(range(16)), cut)].append(solution)
    assert len(grouped) == 36
    assert any(len(group) >= 2 for group in grouped.values())
    for group in grouped.values():
        first = group[0]
        for other in group[1:]:
            # Any valid suffix of one prefix completes every other
            # prefix with exactly the same live obligation signature.
            assert puzzle.valid_solution(other[:cut] + first[cut:])
            assert puzzle.valid_solution(first[:cut] + other[cut:])


@pytest.mark.parametrize("box,side_factorial", [
    (1, 1), (2, 24), (3, 362880), (4, 20922789888000),
])
def test_exact_rank_at_first_row_for_any_generalized_size(
    box: int, side_factorial: int,
) -> None:
    assert exact_first_row_rank(box) == side_factorial
    assert side_factorial == factorial(box * box)


@pytest.mark.parametrize("bad", (True, 0, -2))
def test_invalid_box_order_is_rejected(bad: int) -> None:
    with pytest.raises(ValueError):
        exact_first_row_rank(bad)


def test_rejects_invalid_cut_and_incomplete_prefix_witness() -> None:
    puzzle = Puzzle(2, (0,) * 16)
    solution = completed_four_by_four_grids()[0]
    for cut in (-1, 17, True):
        with pytest.raises(ValueError):
            blank_four_by_four_cut(cut)
    with pytest.raises(ValueError):
        prefix_signature(puzzle, (1,) * 16, tuple(range(16)), 7)
    with pytest.raises(ValueError):
        prefix_signature(puzzle, solution, (0,) * 16, 7)
