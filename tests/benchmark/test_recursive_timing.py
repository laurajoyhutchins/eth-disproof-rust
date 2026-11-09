"""Native pytest-benchmark JSON; results are never reserialized."""
from __future__ import annotations
import os,pytest
from benchmarks.recursive_cases import get_case,IDS,VARIANTS
pytestmark=pytest.mark.benchmark

def chosen():
    selection=os.environ.get('SUDOKU_RECURSIVE_PAIRS')
    all_pairs=[(name,variant) for name in IDS for variant in VARIANTS]
    if selection is None:return all_pairs
    wanted=set(selection.split(','))
    valid={n+':'+v for n,v in all_pairs}
    if not wanted<=valid:raise ValueError(f'unknown pairs: {wanted-valid}')
    return [(n,v) for n,v in all_pairs if n+':'+v in wanted]

@pytest.mark.parametrize('case_id,variant',chosen(),ids=lambda p:p)
def test_recursion(case_id,variant,benchmark):
    rounds=int(os.environ.get('SUDOKU_BENCHMARK_ROUNDS','3'))
    if rounds < 3:
        raise ValueError('SUDOKU_BENCHMARK_ROUNDS must be >= 3')
    case=get_case(case_id,variant)
    case.validate()
    benchmark.group=case_id
    benchmark.extra_info.update({'benchmark.case':case_id,'benchmark.variant':variant,
          'benchmark.parameters':case.parameters,'benchmark.duration.unit':'s',
          'iterations_per_round':1,'warmup_rounds':1,'measurement_rounds':rounds,
          'garbage_collection':'disabled'})
    benchmark.pedantic(lambda op:op(),setup=lambda:((get_case(case_id,variant).run,),{}),
                        iterations=1,rounds=rounds,warmup_rounds=1)
