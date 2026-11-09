"""Independent differential and capacity contracts for weighted ZDD contraction."""
from __future__ import annotations

from math import comb, factorial
from random import Random

import pytest

from non_exponential_sudoku.sudoku.state import prepare_residual
from non_exponential_sudoku.sudoku.frontier import FrontierCapacityError, count_frontier
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from non_exponential_sudoku.sudoku.weighted_zdd import (
    ZDDLimits, _Budget, _Diagram, contract_zdd,
)
from reference.generalized_bench import canonical_solution
from reference.mrv_count import count_mrv_reference
from reference.real_sudoku_bench import puzzles

pytestmark = pytest.mark.checkpoint


def _decode(diagram: _Diagram, root: int) -> dict[int, int]:
    """Testing oracle: explicitly expand the small diagram's weighted sets."""
    if root == 0:
        return {}
    if root < 0:
        return {0: -root}
    bit, lo, hi = diagram.nodes[root]
    result = _decode(diagram, lo)
    for mask, mass in _decode(diagram, hi).items():
        assert mask | 1 << bit not in result
        result[mask | 1 << bit] = mass
    return result


def _encode(diagram: _Diagram, states: dict[int, int]) -> int:
    root = 0
    for mask, weight in states.items():
        term = -weight
        while mask:
            bit = mask & -mask
            mask ^= bit
            term = diagram.force(term, bit.bit_length() - 1)
        root = diagram.add(root, term)
    return root


def test_diagram_algebra_matches_independent_explicit_map() -> None:
    rng = Random(20261110)
    for _ in range(180):
        limit = 8
        states = {rng.randrange(1 << limit): rng.randrange(1, 9)
                  for _ in range(rng.randrange(1, 13))}
        candidates = [rng.randrange(1 << limit) for _ in range(rng.randrange(1, 5))]
        keep = rng.randrange(1 << limit)
        budget = _Budget(ZDDLimits())
        old = _Diagram(budget)
        root = _encode(old, states)
        assert _decode(old, root) == states
        new = _Diagram(budget, old.size)
        next_root = 0
        for candidate in candidates:
            next_root = new.add(next_root, new.transition(old, root, candidate, keep))
        expected: dict[int, int] = {}
        for signature, multiplicity in states.items():
            for candidate in candidates:
                if not signature & candidate:
                    key = (signature | candidate) & keep
                    expected[key] = expected.get(key, 0) + multiplicity
        assert _decode(new, next_root) == expected
        assert new.totals(next_root)[:2] == (sum(expected.values()), len(expected))


def test_sudoku_diagram_agrees_with_separate_search_and_dictionary() -> None:
    empty = Puzzle(2, (0,) * 16)
    for bit_order in ('digit-major', 'unit-major'):
        result = contract_zdd(empty, bit_order=bit_order)
        assert result.count == 288
        assert result.stats.complete
        assert result.stats.final_represented_states == 1
    rng = Random(360036)
    complete = canonical_solution(2)
    for _ in range(34):
        kept = set(rng.sample(range(16), rng.randrange(15)))
        puzzle = Puzzle(2, tuple(d if index in kept else 0
                                 for index, d in enumerate(complete)))
        oracle, _ = count_mrv_reference(puzzle)
        reference = count_frontier(puzzle).count
        assert contract_zdd(puzzle).count == oracle == reference
        assert contract_zdd(puzzle, order='minimum-domain').count == oracle
        # Supplied masks restrict the problem. Compare the same masks, not
        # the unrestricted original puzzle's solution count.
        domains = tuple(1 << (d - 1) if index in kept else
                        15 ^ (1 << rng.randrange(4))
                        for index, d in enumerate(complete))
        restricted = count_frontier(puzzle, domains=domains).count
        assert contract_zdd(puzzle, domains=domains).count == restricted
    assert contract_zdd(Puzzle(2, (1, 1) + (0,) * 14)).count == 0
    assert contract_zdd(Puzzle(1, (1,))).count == 1


def test_unlabeled_empty_nine_by_nine_first_row_is_compressed() -> None:
    empty = Puzzle(3, (0,) * 81)
    row = contract_zdd(empty, prefix_cells=9)
    assert not row.stats.complete
    assert row.stats.free_cells == 81
    assert row.stats.contracted_cells == 9
    assert row.count == factorial(9)
    assert row.stats.final_represented_states == factorial(9)
    assert row.stats.final_nodes == 3648
    assert row.stats.final_nodes * 90 < row.stats.final_represented_states
    assert row.stats.peak_allocated_nodes <= 80_000
    # The same exact operation with the natural unit-major variable order
    # creates much larger intermediate diagrams and refuses under a cap.
    with pytest.raises(FrontierCapacityError, match='allocated-node limit'):
        contract_zdd(empty, prefix_cells=9, bit_order='unit-major',
                     limits=ZDDLimits(max_nodes=50_000))
    pinned = Puzzle(3, (1,) + (0,) * 80)
    eight = contract_zdd(pinned, prefix_cells=8)
    assert eight.count == factorial(8)
    assert not eight.stats.complete


def test_pinned_digits_still_admit_exact_diagram_compression() -> None:
    """All nine clues pin digit names, leaving no S9 digit stabilizer."""
    solved = canonical_solution(3)
    # Fix only the bottom row. Each top-row column forbids its bottom digit;
    # the top row may be any permutation with no fixed position.
    pinned = Puzzle(3, tuple(digit if index // 9 == 8 else 0
                             for index, digit in enumerate(solved)))
    result = contract_zdd(pinned, prefix_cells=9)
    independent = sum((-1)**k * comb(9, k) * factorial(9-k)
                      for k in range(10))
    assert {digit for digit in pinned.entries if digit} == set(range(1, 10))
    assert independent == 133496
    assert result.count == result.stats.final_represented_states == independent
    assert result.stats.final_nodes == 3305
    assert result.stats.final_nodes * 40 < independent
    assert not result.stats.complete


def test_hard_nine_by_nine_negative_control() -> None:
    hard = next(p for name, p, _ in puzzles() if name == '9x9-hard-unique')
    result = contract_zdd(hard)
    assert result.count == 1
    assert result.stats.peak_represented_states == 1261
    # Algebraic compression is not guaranteed: more ZDD nodes than
    # explicit dictionary signatures on this fully labeled puzzle.
    assert result.stats.peak_nodes > result.stats.peak_represented_states
    assert result.stats.complete


def test_resource_refusals_and_input_validation() -> None:
    empty = Puzzle(2, (0,) * 16)
    with pytest.raises(FrontierCapacityError, match='allocated-node limit'):
        contract_zdd(empty, limits=ZDDLimits(max_nodes=1))
    with pytest.raises(FrontierCapacityError, match='algebraic-operation limit'):
        contract_zdd(empty, limits=ZDDLimits(max_operations=1))
    with pytest.raises(FrontierCapacityError, match='estimated-byte limit'):
        contract_zdd(empty, limits=ZDDLimits(max_estimated_bytes=1))
    with pytest.raises(FrontierCapacityError, match='coefficient-bit limit'):
        contract_zdd(empty, limits=ZDDLimits(max_coefficient_bits=1))
    with pytest.raises(ValueError, match='prefix length'):
        contract_zdd(empty, prefix_cells=17)
    with pytest.raises(ValueError, match='prefix length'):
        contract_zdd(empty, prefix_cells=True)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match='cell ordering'):
        contract_zdd(empty, order='whatever')  # type: ignore[arg-type]
    with pytest.raises(ValueError, match='variable ordering'):
        contract_zdd(empty, bit_order='whatever')  # type: ignore[arg-type]
    for limits in ({'max_nodes': 0}, {'max_operations': 0},
                   {'max_estimated_bytes': 0}, {'max_coefficient_bits': 0}):
        with pytest.raises(ValueError, match='ZDD limits must be positive'):
            ZDDLimits(**limits)
