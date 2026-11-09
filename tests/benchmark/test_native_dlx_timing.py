"""Native pytest-benchmark timing for exact-cover propagation; no in-test timers."""
from __future__ import annotations
import os
import pytest
from benchmarks.native_dlx_cases import CASES, prepare

pytestmark=pytest.mark.benchmark


def selected_pairs():
    selection=os.environ.get('SUDOKU_BENCH_PAIRS')
    pairs=[(name,variant) for name,variants in CASES.items() for variant in variants]
    if not selection:
        return pairs
    names=set(selection.split(','))
    missing=names-{name+':'+var for name,var in pairs}
    if missing:
        raise ValueError('Unknown SUDOKU_BENCH_PAIRS: '+repr(sorted(missing)))
    return [(name,var) for name,var in pairs if name+':'+var in names]


@pytest.mark.parametrize('case_id,variant',selected_pairs(),
  ids=[name+'-'+var for name,var in selected_pairs()])
def test_exact_cover_timing(case_id,variant,benchmark):
    case=prepare(case_id,variant)
    case.validate()
    benchmark.group=case_id
    benchmark.extra_info.update({'benchmark.case':case_id,'benchmark.variant':variant,
       'benchmark.parameters':case.parameters,'benchmark.expected':str(case.expected)[:256],
       'benchmark.duration.unit':'s','warmup_rounds':1,'timing_rounds':3,
       'garbage_collection':'disabled','iterations_per_round':1})
    benchmark.pedantic(lambda operation:operation(),
          setup=lambda:((case.operation_factory(),),{}),rounds=3,warmup_rounds=1)
