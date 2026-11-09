"""Sound orbit-mass contraction and finite-field permutation contracts."""
from __future__ import annotations

from non_exponential_sudoku.sudoku.state import initial_domains

from itertools import permutations
from random import Random

import pytest

from non_exponential_sudoku.sudoku.frontier import (
    FrontierCapacityError, FrontierLimits, count_frontier,
)
from non_exponential_sudoku.sudoku.symmetry import (
    contract_digit_orbits, pgl2_f8_permutations, symmetry_for_domains,
)
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.generalized_bench import canonical_solution
from reference.real_sudoku_bench import puzzles

pytestmark = pytest.mark.checkpoint


def test_projective_action_is_sharply_three_transitive() -> None:
    group = pgl2_f8_permutations()
    assert len(group) == 9 * 8 * 7 == 504
    assert len(set(group)) == 504
    assert all(sorted(perm) == list(range(9)) for perm in group)
    assert len({(perm[0], perm[1], perm[2]) for perm in group}) == 504
    assert tuple(range(9)) in group


def test_empty_four_by_four_exact_orbit_count() -> None:
    empty = Puzzle(2, (0,) * 16)
    quotient = contract_digit_orbits(empty)
    assert quotient.solutions == 288
    assert quotient.partial_assignments == 288
    assert quotient.stats.group_order == 24
    assert quotient.stats.peak_orbits == 4
    assert quotient.stats.final_raw_states == 1
    pinned = Puzzle(2, (1,) + (0,) * 15)
    q = contract_digit_orbits(pinned)
    assert q.solutions == count_frontier(pinned).count == 72
    assert q.stats.group_order == 6


def test_random_four_by_four_clues_and_domains_match_unquotiented() -> None:
    rng = Random(20261108)
    answer = canonical_solution(2)
    full = 15
    for _ in range(60):
        indices = rng.sample(range(16), rng.randrange(0, 14))
        entries = tuple(answer[c] if c in indices else 0 for c in range(16))
        puzzle = Puzzle(2, entries)
        ordinary = count_frontier(puzzle)
        quotient = contract_digit_orbits(puzzle)
        assert quotient.solutions == ordinary.count
        assert contract_digit_orbits(puzzle, mode='suffix-permutations').solutions == ordinary.count
        assert quotient.stats.group_order >= 1
        # Arbitrary restrictions change the problem, but quotienting still
        # preserves the exact count of that explicitly restricted problem.
        domains = tuple(
            (1 << (given - 1)) if given else
            (full ^ (1 << rng.randrange(4)))
            for given in entries
        )
        assert (contract_digit_orbits(puzzle, domains=domains).solutions
                == count_frontier(puzzle, domains=domains).count)
        assert (contract_digit_orbits(puzzle, domains=domains,
                                      mode='suffix-permutations').solutions
                == count_frontier(puzzle, domains=domains).count)


def test_pgl_vs_full_digit_group_on_first_row_of_empty_9x9() -> None:
    puzzle = Puzzle(3, (0,) * 81)
    full = contract_digit_orbits(puzzle, max_cells=9)
    projective_fourth = contract_digit_orbits(puzzle, mode='pgl2', max_cells=4)
    assert projective_fourth.stats.final_orbits == 6  # Cross-ratio classes.
    projective = contract_digit_orbits(puzzle, mode='pgl2', max_cells=9)
    assert full.solutions is None  # Prefix assignments, not solutions.
    assert projective.solutions is None
    assert full.stats.group_order == 362880
    assert projective.stats.group_order == 504
    assert full.stats.final_orbits == 1
    assert projective.stats.final_orbits == 720
    assert full.stats.final_raw_states == projective.stats.final_raw_states == 362880
    assert full.partial_assignments == projective.partial_assignments == 362880


def test_two_empty_9x9_rows_have_independent_count_oracle() -> None:
    puzzle = Puzzle(3, (0,) * 81)
    quotient = contract_digit_orbits(puzzle, max_cells=18)
    first = tuple(range(9))
    second_rows = sum(
        not any(a == b for a, b in zip(first, second))
        and not any(set(first[c:c+3]) & set(second[c:c+3])
                    for c in (0, 3, 6))
        for second in permutations(range(9))
    )
    assert second_rows == 12096
    assert quotient.solutions is None
    assert quotient.partial_assignments == 362880 * second_rows == 4389396480
    assert quotient.stats.final_orbits == 4860


def test_hard_puzzle_has_no_digit_stabilizer_to_exploit() -> None:
    _, puzzle, expected = next(x for x in puzzles()
                               if x[0] == '9x9-hard-unique')
    domains = initial_domains(puzzle)
    assert domains is not None
    assert symmetry_for_domains(domains, 9).order == 1
    assert symmetry_for_domains(domains, 9, 'pgl2').order == 1
    assert contract_digit_orbits(puzzle).solutions == expected == 1
    assert contract_digit_orbits(puzzle, mode='pgl2').solutions == expected
    adaptive = contract_digit_orbits(puzzle, mode='suffix-permutations')
    assert adaptive.solutions == expected
    assert adaptive.stats.peak_orbits == 1261  # No benefit at its bottleneck.
    assert adaptive.stats.group_order == 1
    assert adaptive.stats.final_group_order == 362880


def test_no_unsafe_group_or_undisclosed_partial_count() -> None:
    empty = Puzzle(2, (0,) * 16)
    with pytest.raises(ValueError, match='precisely nine'):
        contract_digit_orbits(empty, mode='pgl2')
    with pytest.raises(ValueError, match='nonnegative'):
        contract_digit_orbits(empty, max_cells=-1)
    with pytest.raises(ValueError, match='Invalid domain'):
        contract_digit_orbits(empty, domains=(0,) + (15,) * 15)
    with pytest.raises(ValueError, match='contradicts given'):
        contract_digit_orbits(Puzzle(2, (1,) + (0,) * 15), domains=(2,) + (15,) * 15)
    with pytest.raises(FrontierCapacityError, match='state limit'):
        contract_digit_orbits(Puzzle(3, (0,) * 81), max_cells=10,
                              limits=FrontierLimits(max_states=1))
    with pytest.raises(FrontierCapacityError, match='transition limit'):
        contract_digit_orbits(empty, limits=FrontierLimits(max_transitions=1))
    with pytest.raises(FrontierCapacityError, match='estimated-byte limit'):
        contract_digit_orbits(empty, limits=FrontierLimits(max_estimated_bytes=1))


def test_projective_point_stabilizers_and_suffix_advantage() -> None:
    # Fixing three labeled points forces the identity in sharply
    # three-transitive PGL2(F8), even though S9 still has 6! elements.
    for pinned, expected_pgl in ((1, 56), (2, 7), (3, 1)):
        masks = tuple(1 << digit for digit in range(pinned)) + (511,) * (81 - pinned)
        assert symmetry_for_domains(masks, 9, 'pgl2').order == expected_pgl
    _, puzzle, expected = next(x for x in puzzles()
                               if x[0] == '9x9-77-givens-two-solutions')
    global_result = contract_digit_orbits(puzzle)
    suffix_result = contract_digit_orbits(puzzle, mode='suffix-permutations')
    assert global_result.solutions == suffix_result.solutions == expected
    assert global_result.stats.group_order == 1
    assert suffix_result.stats.group_order == 10080
    assert suffix_result.stats.peak_orbits < global_result.stats.peak_orbits
