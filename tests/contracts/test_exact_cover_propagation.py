"""Independent matching comparison and exact-cover propagation contracts."""
from __future__ import annotations
import random
import pytest
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.generalized_bench import canonical_solution
from reference.real_sudoku_bench import puzzles
from reference.local_support import projected_domains,pin_band_wires,LocalContradiction
from reference.exact_cover_propagation import (ExactCoverPropagation,
    PropagationLimits,PropagationCapacityError,ExactCoverContradiction)

pytestmark=pytest.mark.checkpoint


def test_fixed_points_match_original_matching_projection():
    for name,puzzle,expected in puzzles():
        if 'hard-' in name or 'easy-' in name or 'contradictory' in name:
            continue
        original,_=projected_domains(puzzle,method='matching')
        enhanced,_,data=projected_domains(puzzle,method='enhanced',return_metrics=True)
        incremental,_=projected_domains(puzzle,method='incremental')
        assert enhanced==original, name
        assert all(a & b==a for a,b in zip(enhanced,incremental)),name
        assert data['remaining_candidates']==sum(x.bit_count() for x in original)
        assert data['initial_candidates']==puzzle.side**3


def test_random_clue_subsets_are_equivalent():
    rng=random.Random(6601)
    for b,amounts in [(2,(4,8,12)),(3,(52,64,75))]:
        solution=canonical_solution(b)
        for amount in amounts:
            for repeat in range(4):
                clues=rng.sample(range(len(solution)),amount)
                entries=tuple(solution[j] if j in clues else 0 for j in range(len(solution)))
                puzzle=Puzzle(b,entries)
                baseline,_=projected_domains(puzzle,method='matching')
                enhanced,_=projected_domains(puzzle,method='enhanced')
                assert baseline==enhanced,(b,amount,repeat)


def test_incremental_support_counts_and_idempotence():
    puzzle=Puzzle(2,(0,)*16)
    state=ExactCoverPropagation(puzzle)
    assert len(state.rows)==64
    assert len(state.columns)==64
    assert all(len(row)==4 for row in state.rows)
    assert all(sum(state.active[row] for row in rows)==state.supports[i]
               for i,rows in enumerate(state.columns))
    row=0
    assert state.select(row)
    state.propagate_forced()
    assert not state.select(row)
    assert state.domains[0]==1
    assert all(sum(state.active[r] for r in rs)==state.supports[i]
               for i,rs in enumerate(state.columns))
    assert state.metrics()['removed_candidates']>0
    assert all(rows>0 and cols>0 for rows,cols in state.connected_components())


def test_zero_support_and_conflicting_clues():
    conflict=Puzzle.from_text('11'+'.'*14,2)
    for method in ('matching','incremental','enhanced'):
        with pytest.raises(LocalContradiction):
            projected_domains(conflict,method=method)
    state=ExactCoverPropagation(Puzzle(2,(0,)*16))
    for digit in range(1,4):
        state.remove_cell_digit(0,digit)
    assert state.domains[0]==8
    with pytest.raises(ExactCoverContradiction):
        state.remove_cell_digit(0,4)


def test_capacity_limits_fail_closed():
    puzzle=Puzzle(2,(1,)+(0,)*15)
    with pytest.raises(PropagationCapacityError,match='candidate limit'):
        ExactCoverPropagation(puzzle,limits=PropagationLimits(max_candidates=8))
    with pytest.raises(PropagationCapacityError,match='support-update limit'):
        ExactCoverPropagation(puzzle,limits=PropagationLimits(max_updates=1))


def test_matching_projection_never_calls_exponential_search():
    puzzle=Puzzle(2,(0,)*16)
    state=ExactCoverPropagation(puzzle)
    assert state.metrics()['matching_checks']==0
    assert state.connected_components()


def test_reduced_network_preserves_exact_solution_counts_and_witness():
    for name,puzzle,count in puzzles():
        if name not in ('4x4-12-givens-two-solutions',
                        '9x9-73-givens-four-solutions'):
            continue
        baseline,_=pin_band_wires(puzzle,propagation='matching')
        faster,info=pin_band_wires(puzzle,propagation='enhanced')
        assert baseline.edges==faster.edges==(4 if count==2 else 8)
        assert info['propagation']['matching_checks']>=0


def test_matching_prunes_supported_hall_structure_beyond_singles():
    # Three compatible clues create a genuine all-different support reduction
    # that cannot be obtained through forced placements alone.
    puzzle=Puzzle(2,(1,0,3,0,3,0,0,0,0,0,0,0,0,0,0,0))
    incremental,_=projected_domains(puzzle,method='incremental')
    enhanced,_=projected_domains(puzzle,method='enhanced')
    reference,_=projected_domains(puzzle,method='matching')
    assert enhanced==reference
    assert sum(x.bit_count() for x in incremental)==41
    assert sum(x.bit_count() for x in enhanced)==37
