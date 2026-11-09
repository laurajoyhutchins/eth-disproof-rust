"""Bounded observational trace; no inference of safe cross-oracle memoization."""
from time import perf_counter_ns

import pytest

from non_exponential_sudoku import ContractionEngine, WorkTrace
from benchmarks.recursive_cases import get_case

pytestmark = pytest.mark.checkpoint


def test_trace_distinguishes_repeated_structure_from_candidate_exact_inputs():
    trace = WorkTrace(max_events=2, max_keys=2)
    for key in (1, 2, 1, 3):
        trace.observe(operation="packet", topology=("same",), exact_input=(key,),
                      started_ns=perf_counter_ns(), output=(1, 2), cache_hit=key == 1)
    result = trace.report()
    assert result["operation_counts"] == {"packet": 4}
    assert result["tracked_unique_topologies"] == 1
    assert result["repeated_topologies"] == {"packet": 3}
    assert result["tracked_unique_exact_input_candidates"] == 2
    assert result["repeated_exact_input_candidates"] == {"packet": 1}
    assert result["unclassified_exact_inputs"] == {"packet": 1}
    assert result["cache_hits"] == {"packet": 2}
    assert result["truncation"]["events"] == 2
    assert len(result["events"]) == 2
    assert result["events"][0]["start_offset_ns"] <= result["events"][0]["end_offset_ns"]


def test_trace_budget_validation():
    with pytest.raises(ValueError, match="positive"):
        WorkTrace(max_events=0)
    with pytest.raises(ValueError, match="positive"):
        WorkTrace(max_keys=0)


def test_trace_preserves_recursive_exact_result_and_exposes_packet_work():
    case = get_case("nested-2wire", "plans")
    baseline = ContractionEngine(case.config).contract(case.network)
    trace = WorkTrace(max_events=256, max_keys=256)
    engine = ContractionEngine(case.config, work_trace=trace)
    assert engine.contract(case.network) == baseline
    report = trace.report()
    assert report["operation_counts"]["child_contraction"] > 0
    assert report["operation_counts"]["packet"] > 0
    assert report["tracked_unique_topologies"] > 0
    assert all(e["elapsed_ns"] >= 0 for e in report["events"])
    assert report["truncation"]["events"] >= 0

def test_trace_never_calls_repr_on_structured_exact_inputs() -> None:
    class NoRepr:
        def __repr__(self) -> str:
            raise AssertionError("exact inputs must not be rendered as text")

    value = NoRepr()
    trace = WorkTrace(max_events=3, max_keys=2)
    for index in (0, 0, 1):
        trace.observe(operation="packet", topology=("ports", (0, 1)),
                      exact_input=(value, index),
                      started_ns=perf_counter_ns(), output=(42,))
    assert trace.report()["repeated_exact_input_candidates"] == {"packet": 1}
    assert trace.events[0].topology_id == trace.events[1].topology_id
    assert trace.events[0].input_id == trace.events[1].input_id
    assert trace.events[0].input_id != trace.events[2].input_id
