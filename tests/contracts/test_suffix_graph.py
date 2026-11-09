"""Exact residual-graph automorphism tests, with independent 4x4 oracle."""
from __future__ import annotations

from non_exponential_sudoku.sudoku.state import initial_domains, candidate_bits

from itertools import permutations, product
from random import Random

import pytest

from non_exponential_sudoku.sudoku.frontier import (
    FrontierCapacityError, FrontierLimits, count_frontier,
)
from non_exponential_sudoku.sudoku.suffix_graph import (
    SuffixGraphLimits, _certify_suffix_action,
    _geometric_generators, count_suffix_graph,
)
from non_exponential_sudoku.sudoku.symmetry import symmetry_for_domains
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.generalized_bench import canonical_solution
from reference.real_sudoku_bench import puzzles

# Each test has one primary tier. Graph-isomorphism discovery is integration;
# lightweight certificates remain in the per-commit checkpoint.


def _all_four_by_four() -> tuple[tuple[int, ...], ...]:
    rows = tuple(permutations(range(1, 5)))
    answer = []
    for matrix in product(rows, repeat=4):
        board = tuple(d for row in matrix for d in row)
        if all({board[4*r+c] for r in range(4)} == {1, 2, 3, 4}
               for c in range(4)) and all(
            {board[r*4+c] for r in range(br, br + 2)
             for c in range(bc, bc + 2)} == {1, 2, 3, 4}
            for br in (0, 2) for bc in (0, 2)
        ):
            answer.append(board)
    return tuple(answer)


@pytest.mark.integration
def test_empty_four_by_four_and_exact_reference() -> None:
    empty = Puzzle(2, (0,) * 16)
    assert len(_all_four_by_four()) == 288
    baseline = count_suffix_graph(empty, mode='none')
    geometry = count_suffix_graph(empty, mode='geometry')
    incidence = count_suffix_graph(empty, mode='incidence')
    assert baseline.count == geometry.count == incidence.count == 288
    assert baseline.stats.memo_states == 549
    assert geometry.stats.memo_states < 130
    assert incidence.stats.memo_states < geometry.stats.memo_states
    assert incidence.stats.graph_isomorphisms_examined > 0
    assert geometry.stats.nontrivial_canonicalizations > 0


@pytest.mark.integration
def test_all_digits_fixed_but_suffix_graph_still_has_symmetry() -> None:
    solved = canonical_solution(2)
    # One clue for each digit. No nonidentity global digit permutation remains.
    indices = (0, 4, 8, 12)
    puzzle = Puzzle(2, tuple(solved[i] if i in indices else 0
                             for i in range(16)))
    initial = initial_domains(puzzle)
    assert initial is not None
    assert symmetry_for_domains(initial, 4).order == 1
    independent = sum(all(not clue or clue == digit
                          for clue, digit in zip(puzzle.entries, solution))
                      for solution in _all_four_by_four())
    assert independent == 12
    baseline = count_suffix_graph(puzzle, mode='none')
    geometry = count_suffix_graph(puzzle, mode='geometry')
    incidence = count_suffix_graph(puzzle, mode='incidence')
    assert baseline.count == geometry.count == incidence.count == independent
    assert baseline.stats.memo_states == 63
    assert geometry.stats.memo_states < baseline.stats.memo_states
    assert incidence.stats.memo_states < geometry.stats.memo_states
    assert incidence.stats.peak_states_at_depth < baseline.stats.peak_states_at_depth


@pytest.mark.checkpoint
def test_automorphism_can_move_first_cell_because_we_cache_continuations() -> None:
    empty = Puzzle(2, (0,) * 16)
    initial = initial_domains(empty)
    assert initial is not None
    # Some admissible symmetries move the first cell to a different cell.
    # These are sound for continuation values, but not for forward masses.
    generators = _geometric_generators(empty, tuple(range(16)), initial)
    assert generators
    assert any(permutation != tuple(range(48)) for permutation in generators)
    assert count_suffix_graph(empty, mode='geometry').count == 288


@pytest.mark.integration
def test_randomized_counts_against_independent_four_by_four_enumeration() -> None:
    solutions = _all_four_by_four()
    rng = Random(20261108)
    for _ in range(42):
        solution = rng.choice(solutions)
        clues = set(rng.sample(range(16), rng.randrange(0, 14)))
        entries = tuple(solution[i] if i in clues else 0 for i in range(16))
        puzzle = Puzzle(2, entries)
        expected = sum(all(not clue or clue == digit
                           for clue, digit in zip(entries, candidate))
                       for candidate in solutions)
        assert count_suffix_graph(puzzle, mode='geometry').count == expected
        # Arbitrary cell domains define a different, explicitly restricted
        # counting problem. Compare those as well with the independent oracle.
        domains = tuple(1 << (given - 1) if given else
                        15 ^ (1 << rng.randrange(4))
                        for given in entries)
        restricted = sum(all(domains[i] & (1 << (digit - 1))
                             for i, digit in enumerate(candidate))
                         for candidate in solutions)
        assert count_suffix_graph(puzzle, domains=domains).count == restricted
    for _ in range(9):
        indices = set(rng.sample(range(16), 7))
        entries = tuple(solutions[0][i] if i in indices else 0
                        for i in range(16))
        puzzle = Puzzle(2, entries)
        assert count_suffix_graph(puzzle, mode='incidence').count == count_frontier(puzzle).count


@pytest.mark.integration
def test_real_hard_9x9_no_false_positive_compression() -> None:
    _, puzzle, expected = next(item for item in puzzles()
                               if item[0] == '9x9-hard-unique')
    plain = count_suffix_graph(puzzle, mode='none')
    geometric = count_suffix_graph(puzzle, mode='geometry')
    assert plain.count == geometric.count == expected == 1
    assert plain.stats.memo_states == geometric.stats.memo_states == 13_861
    assert geometric.stats.peak_states_at_depth == 1261
    assert geometric.stats.nontrivial_canonicalizations == 0


@pytest.mark.checkpoint
def test_invalid_automorphism_rejected_by_independent_certificate() -> None:
    # Two options with distinct triple-bit signatures. Swapping only one bit
    # cannot preserve the candidate hypergraph.
    options = {0: (candidate_bits(0, 0, 4, 2),
                   candidate_bits(0, 1, 4, 2))}
    bad = list(range(48))
    bad[0], bad[1] = bad[1], bad[0]
    with pytest.raises(ValueError, match='candidate hyperedges'):
        _certify_suffix_action((0,), options, {0: 0}, tuple(bad))
    with pytest.raises(ValueError, match='remaining cells'):
        _certify_suffix_action((0,), options, {0: 1}, tuple(range(48)))


@pytest.mark.checkpoint
def test_fail_closed_limits_and_input_validation() -> None:
    empty = Puzzle(2, (0,) * 16)
    with pytest.raises(FrontierCapacityError, match='memo state limit'):
        count_suffix_graph(empty, mode='none', limits=SuffixGraphLimits(
            frontier=FrontierLimits(max_states=1)))
    with pytest.raises(FrontierCapacityError, match='transition limit'):
        count_suffix_graph(empty, mode='none', limits=SuffixGraphLimits(
            frontier=FrontierLimits(max_transitions=1)))
    with pytest.raises(FrontierCapacityError, match='orbit limit'):
        count_suffix_graph(empty, mode='geometry', limits=SuffixGraphLimits(max_orbit=1))
    with pytest.raises(FrontierCapacityError, match='cache limit'):
        count_suffix_graph(empty, mode='geometry', limits=SuffixGraphLimits(max_orbit_cache_entries=1))
    with pytest.raises(FrontierCapacityError, match='recursion depth'):
        count_suffix_graph(empty, limits=SuffixGraphLimits(max_recursive_cells=1))
    with pytest.raises(FrontierCapacityError, match='estimated-byte limit'):
        count_suffix_graph(empty, limits=SuffixGraphLimits(frontier=FrontierLimits(max_estimated_bytes=1)))
    with pytest.raises(ValueError, match='Unknown suffix graph mode'):
        count_suffix_graph(empty, mode='bogus')  # type: ignore[arg-type]
    with pytest.raises(ValueError, match='Invalid domain'):
        count_suffix_graph(empty, domains=(0,) + (15,) * 15)
    with pytest.raises(ValueError, match='contradicts given'):
        count_suffix_graph(Puzzle(2, (1,) + (0,) * 15), domains=(2,) + (15,) * 15)
    with pytest.raises(ValueError, match='positive'):
        SuffixGraphLimits(max_generators=0)


@pytest.mark.checkpoint
def test_single_cell_and_contradictory_clue_inputs() -> None:
    assert count_suffix_graph(Puzzle(1, (0,)), mode='geometry').count == 1
    assert count_suffix_graph(Puzzle(1, (1,)), mode='incidence').count == 1
    puzzle = Puzzle(2, (1, 1) + (0,) * 14)
    assert count_suffix_graph(puzzle).count == 0
    with pytest.raises(ValueError, match='Invalid Sudoku puzzle'):
        count_suffix_graph(Puzzle(2, (5,) + (0,) * 15))


@pytest.mark.checkpoint
def test_nearly_complete_generalized_sudoku() -> None:
    name, puzzle, expected = next(item for item in puzzles()
                                  if item[0] == '16x16-252-givens-two-solutions')
    assert name
    assert count_suffix_graph(puzzle, mode='none').count == expected == 2
    assert count_suffix_graph(puzzle, mode='geometry').count == expected


@pytest.mark.checkpoint
def test_graph_mode_respects_explicit_search_limits() -> None:
    empty = Puzzle(2, (0,) * 16)
    bounded = count_suffix_graph(empty, mode='incidence', limits=SuffixGraphLimits(
        max_graph_choices=1, max_graph_isomorphisms=1, max_generators=1,
    ))
    assert bounded.count == 288
