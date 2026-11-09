"""Complete recursive Sudoku counts and witness recovery with both kernels."""
import pytest
from reference.real_sudoku_bench import puzzles
from reference.sudoku_paper_solver import paper_count,solve

pytestmark=pytest.mark.integration


def test_both_kernels_count_four_completions_exactly():
    puzzle=next(p for name,p,_ in puzzles() if name=='9x9-73-givens-four-solutions')
    results=[]
    for native in (False,True):
        count,stats=paper_count(puzzle,recovery='jet',propagation='enhanced',native_sparse=native)
        assert count==4
        results.append((count,stats['mode_dp_operations'],stats['child_networks']))
    assert results[0]==results[1]


def test_incremental_and_enhanced_keep_valid_witness():
    puzzle=next(p for name,p,_ in puzzles() if name=='4x4-12-givens-two-solutions')
    for method in ('incremental','enhanced'):
        response=solve(puzzle,propagation=method,recovery='jet')
        assert response['status']=='solved'
        assert response['count']==2
        solution=tuple('123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'.index(c)+1 for c in response['solution'])
        assert puzzle.valid_solution(solution)
