"""Exact contraction and bounded sampling contracts for joint ZDD ordering."""
from __future__ import annotations

from random import Random

import pytest

from non_exponential_sudoku.sudoku.frontier import FrontierCapacityError
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from non_exponential_sudoku.sudoku.weighted_zdd import (
    ZDDLimits, ZDDOrderLimits, _Budget, _Diagram, contract_zdd,
)
from reference.generalized_bench import canonical_solution
from reference.mrv_count import count_mrv_reference
from reference.real_sudoku_bench import puzzles

# Each contract has exactly one verification tier. Expensive reference cases
# run in integration; small exact and refusal contracts remain checkpoint.


def _encode(diagram: _Diagram, states: dict[int, int]) -> int:
    root = 0
    for signature, weight in states.items():
        term = -weight
        mask = signature
        while mask:
            bit = mask & -mask
            mask ^= bit
            term = diagram.force(term, bit.bit_length() - 1)
        root = diagram.add(root, term)
    return root


@pytest.mark.checkpoint
def test_zdd_support_sampling_is_exact_without_enumeration() -> None:
    rng = Random(370037)
    for _ in range(55):
        states = {rng.randrange(1 << 11): rng.randrange(1, 20)
                  for _ in range(rng.randrange(1, 45))}
        zdd = _Diagram(_Budget(ZDDLimits()))
        root = _encode(zdd, states)
        for size in (1, 2, 4, 13, 100):
            signatures = zdd.sample_support(root, size)
            assert len(signatures) == min(size, len(states))
            assert len(set(signatures)) == len(signatures)
            assert set(signatures).issubset(states)
        assert zdd.sample_support(0, 20) == ()
    # Support cardinality is factorially large, but the sampler visits only
    # diagram nodes and sampled paths, never creates the complete dictionary.
    puzzle = Puzzle(3, (0,) * 81)
    result = contract_zdd(puzzle, prefix_cells=9)
    assert result.count == 362880
    assert result.stats.final_nodes == 3648


@pytest.mark.checkpoint
def test_joint_ordering_preserves_small_exact_counts() -> None:
    rng = Random(3711)
    full = canonical_solution(2)
    modes = ('digit-major', 'digit-activity', 'digit-incidence')
    for _ in range(18):
        retained = set(rng.sample(range(16), rng.randrange(16)))
        puzzle = Puzzle(2, tuple(d if i in retained else 0
                                 for i, d in enumerate(full)))
        expected, _ = count_mrv_reference(puzzle)
        for bit_order in modes:
            result = contract_zdd(puzzle, order='reachable', bit_order=bit_order)
            assert result.count == expected
            assert result.stats.complete
            assert result.stats.pilot_evaluations > 0 or result.stats.free_cells == 0
    assert contract_zdd(Puzzle(2, (0,) * 16), order='reachable').count == 288
    assert contract_zdd(Puzzle(2, (1, 1) + (0,) * 14),
                        order='reachable').count == 0


@pytest.mark.checkpoint
def test_joint_order_beats_row_major_nodes_on_hard_nine() -> None:
    hard = next(p for name, p, _ in puzzles() if name == '9x9-hard-unique')
    old = contract_zdd(hard)
    joint = contract_zdd(hard, order='reachable', bit_order='digit-incidence')
    assert old.count == joint.count == 1
    assert old.stats.peak_nodes == 5982
    assert joint.stats.peak_nodes == 2132
    assert joint.stats.peak_nodes * 3 < old.stats.peak_nodes * 2
    assert joint.stats.pilot_transitions > 0
    assert joint.stats.pilot_samples > 0
    assert joint.stats.peak_represented_states > 0


@pytest.mark.integration
def test_hard_sixteen_joint_zdd_fits_default_budget() -> None:
    solved = canonical_solution(4)
    retained = set(Random(1).sample(range(256), 120))
    puzzle = Puzzle(4, tuple(d if i in retained else 0
                             for i, d in enumerate(solved)))
    expected, _ = count_mrv_reference(puzzle)
    assert expected == 177
    with pytest.raises(FrontierCapacityError, match='allocated-node limit'):
        contract_zdd(puzzle)
    result = contract_zdd(puzzle, order='reachable', bit_order='digit-incidence')
    assert result.count == expected
    assert result.stats.complete
    assert result.stats.peak_nodes == 13517
    assert result.stats.algebraic_operations < 5_000_000
    assert result.stats.pilot_transitions < 1_000_000


@pytest.mark.checkpoint
def test_order_refuses_all_pilot_limits_without_fallback() -> None:
    puzzle = Puzzle(2, (0,) * 16)
    with pytest.raises(FrontierCapacityError, match='ordering pilot transition'):
        contract_zdd(puzzle, order='reachable', ordering_limits=ZDDOrderLimits(
            max_pilot_transitions=1))
    with pytest.raises(FrontierCapacityError, match='ordering evaluation'):
        contract_zdd(puzzle, order='reachable', ordering_limits=ZDDOrderLimits(
            max_order_evaluations=1))
    with pytest.raises(FrontierCapacityError, match='algebraic-operation'):
        contract_zdd(puzzle, order='reachable', limits=ZDDLimits(max_operations=1))
    with pytest.raises(FrontierCapacityError, match='allocated-node'):
        contract_zdd(puzzle, order='reachable', limits=ZDDLimits(max_nodes=1))
    with pytest.raises(ValueError, match='Unknown ZDD cell ordering'):
        contract_zdd(puzzle, order='invalid')  # type: ignore[arg-type]
    with pytest.raises(ValueError, match='Unknown ZDD variable ordering'):
        contract_zdd(puzzle, bit_order='invalid')  # type: ignore[arg-type]
    for invalid in (
        {'max_pilot_transitions': 0}, {'max_order_evaluations': 0},
        {'pilot_sample_states': 0}, {'pilot_candidate_cells': 0},
    ):
        with pytest.raises(ValueError, match='Invalid ZDD ordering limits'):
            ZDDOrderLimits(**invalid)
