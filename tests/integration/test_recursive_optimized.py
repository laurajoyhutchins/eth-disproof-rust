"""High-fidelity count and witness recovery with optimized recursion."""
from __future__ import annotations
import pytest
from non_exponential_sudoku import RecursionConfig
from reference.real_sudoku_bench import puzzles
from reference.sudoku_paper_solver import paper_count,solve
from benchmarks.recursive_cases import get_case

pytestmark=pytest.mark.integration

OPT=RecursionConfig(child_plans=True,native_packet=True,native_leaf=True,
                    packet_memo_entries=128,packet_memo_bytes=1<<20)

def test_9x9_solution_counts_match_reference_kernel():
    pytest.importorskip('native_recursive')
    for size in ('sudoku-4wire','sudoku-8wire'):
        baseline,original=get_case(size,'reference').validate()
        native,measured=get_case(size,'memo-all').validate()
        assert baseline==native
        assert original.mode_dp_operations==measured.mode_dp_operations
        assert original.child_networks==measured.child_networks
        assert original.recursive_calls==measured.recursive_calls

def test_self_reduction_witness_unchanged_for_sudoku():
    pytest.importorskip('native_recursive')
    puzzle=next(p for name,p,_ in puzzles() if name=='4x4-12-givens-two-solutions')
    baseline=solve(puzzle,propagation='enhanced',recovery='jet')
    optimized=solve(puzzle,propagation='enhanced',recovery='jet',recursion=OPT)
    assert optimized['count']==baseline['count']==2
    assert optimized['solution']==baseline['solution']
    solution=tuple('123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'.index(c)+1 for c in optimized['solution'])
    assert puzzle.valid_solution(solution)

def test_memo_disabled_if_coefficient_value_exceeds_memory_budget():
    pytest.importorskip('native_recursive')
    puzzle=next(p for name,p,_ in puzzles() if name=='9x9-77-givens-two-solutions')
    tiny=RecursionConfig(packet_memo_entries=128,packet_memo_bytes=1)
    count,stats=paper_count(puzzle,recovery='jet',recursion=tiny)
    assert count==2
    assert stats['packet_entry_memo_hits']==0
    assert stats['packet_entry_memo_misses']==0
