"""Inductive call-count bound: distinct from an ETH runtime theorem."""
from __future__ import annotations

from dataclasses import replace

import pytest

from benchmarks.recursive_cases import get_case
from non_exponential_sudoku import ContractionEngine, ContractorConfig, LeafConfig
from reference.recurrence_calls import recursive_call_bound

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize("case_id", ["parity-2wire", "nested-2wire", "crossing-4wire"])
def test_bound_dominate_observed_recursive_calls(case_id: str) -> None:
    case = get_case(case_id, "plans")
    engine = ContractionEngine(case.config)
    assert engine.contract(case.network)[0] == case.expected
    assert engine.stats.recursive_calls <= recursive_call_bound(case.config, case.network.edges)


def test_literal_paper_schedule_is_inactive_for_practical_parameters() -> None:
    # The first possible u_0 > 0 needs lambda >= 131072.  The least
    # qualifying integer s is 2**131071+1, not a practical wire count.
    threshold = 1 << 131071
    almost = ContractorConfig(s=threshold, precision=3, schedule="paper")
    first = ContractorConfig(s=threshold + 1, precision=3, schedule="paper")
    assert recursive_call_bound(almost, 10) == 1
    assert recursive_call_bound(first, 10) == 1  # still below the leaf threshold
    assert recursive_call_bound(first, first.s) > 1


def test_call_bound_rejects_invalid_inputs() -> None:
    config = ContractorConfig(s=3, precision=3, schedule="micro")
    with pytest.raises(ValueError):
        recursive_call_bound(config, -1)
    with pytest.raises(ValueError):
        recursive_call_bound(config, 1, depth=-1)
