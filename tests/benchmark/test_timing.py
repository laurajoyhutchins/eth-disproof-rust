"""Native pytest-benchmark measurements: setup/validation are outside the timer."""
import os
import pytest
from benchmarks.cases import selected_case_ids, prepare_case

pytestmark = pytest.mark.benchmark


@pytest.mark.parametrize('case_id', selected_case_ids(), ids=selected_case_ids())
def test_timing(case_id, benchmark):
    case = prepare_case(case_id)
    # Explicit correctness gates run separately before this file. This assertion
    # is also outside the timed region to protect direct test invocation.
    case.validate()
    rounds = int(os.environ.get('SUDOKU_BENCH_ROUNDS', '7'))
    warmup = int(os.environ.get('SUDOKU_BENCH_WARMUP', '2'))
    benchmark.group = case_id
    benchmark.extra_info.update({
        'benchmark.case': case_id,
        'benchmark.parameters': case.parameters,
        'benchmark.expected': case.expected,
        'benchmark.duration.unit': 's',
        'benchmark.operations.unit': '{operation}',
        'garbage_collection': 'disabled-by-pytest-benchmark-option',
        'warmup_rounds': warmup,
        'timing_rounds': rounds,
        'iterations_per_round': 1,
    })
    def setup():
        return ((case.new_operation(),), {})
    # Only invoke the prepared operation within the timed region. No fixture
    # building, oracle verification, or result checking inside the timed target.
    benchmark.pedantic(lambda operation: operation(),
                       setup=setup, rounds=rounds, warmup_rounds=warmup)
