"""TDD: valuation pruning must reduce work, not just rearrange storage.

The lightweight contracts run in checkpoint. Fresh-process A/B differential
checks run only in the opt-in valuation-scaling workflow.
"""
from __future__ import annotations

from dataclasses import replace

import pytest

from benchmarks.valuation_scaling import CASES, compare_rows, make_case, run_sample
from reference.legacy_mode_catalog import original_catalog
from reference.global_mode_support import exact_weighted_assignment_count
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.packing import pack

pytestmark = pytest.mark.checkpoint


def test_same_packet_geometry_and_precision_on_both_arms() -> None:
    for label in ("center-L4-p5-n2", "center-L8-p11-n2",
                  "recursive-p5", "recursive-p7"):
        spec = make_case(label)
        assert spec.precision >= 5
        assert spec.expected > 0
        assert spec.network.edges >= 2


def test_independent_legacy_catalog_support_is_no_smaller() -> None:
    case = make_case("center-L4-p9-n2")
    assert case.labels is not None
    packing = pack(case.network, 2, case.slot_exponent, case.labels)
    legacy = original_catalog(case.network, packing, 1, case.precision)
    improved = mode_catalog(case.network, packing, 1, case.precision)
    assert all(m.weight >= 1 for m in improved)
    assert len(improved) <= len(legacy)
    old_count = exact_weighted_assignment_count(
        tuple(m.weight for m in legacy),
        tuple(len(m.rows) for m in legacy), case.precision)
    new_count = exact_weighted_assignment_count(
        tuple(m.weight for m in improved),
        tuple(len(m.rows) for m in improved), case.precision)
    assert 0 < new_count <= old_count
    assert new_count < old_count


def test_real_recurrence_uses_original_and_pruned_weights_with_exact_result() -> None:
    old = run_sample("recursive-p5", "original")
    new = run_sample("recursive-p5", "pruned")
    assert old["status"] == new["status"] == "verified"
    summary = compare_rows([old, new], required_cases=("recursive-p5",))
    assert summary["status"] == "verified"
    assert summary["comparisons"][0]["exact_equal"]
    assert summary["comparisons"][0]["old_total_modes"] >= summary["comparisons"][0]["new_total_modes"]


def test_refusal_is_not_misreported_as_equivalent_or_faster() -> None:
    old = run_sample("center-L4-p5-n2", "original")
    newer = run_sample("center-L4-p5-n2", "pruned")
    assert old["status"] == newer["status"] == "verified"
    refused = {**old, "status": "capacity_refused", "actual": None}
    summary = compare_rows([refused, newer], required_cases=("center-L4-p5-n2",))
    assert summary["status"] == "incomplete"
    assert not summary["comparisons"][0]["exact_equal"]
    assert summary["comparisons"][0]["work_reduction"] is None
