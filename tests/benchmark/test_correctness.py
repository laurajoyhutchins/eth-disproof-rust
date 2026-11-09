"""Independent correctness gate for the canonical performance cases."""
import json
import pytest
from benchmarks.cases import selected_case_ids, prepare_case

pytestmark = pytest.mark.benchmark


@pytest.mark.parametrize('case_id', selected_case_ids(), ids=selected_case_ids())
def test_correctness(case_id, record_property):
    record_property('benchmark.case', case_id)
    case = prepare_case(case_id)
    record_property('benchmark.parameters', json.dumps(case.parameters, sort_keys=True))
    record_property('benchmark.independent_oracle', case.independent_oracle)
    assert case.validate() == case.expected
