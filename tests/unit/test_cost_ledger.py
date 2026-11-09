"""An observed cost recurrence must reconcile with actual solver execution."""
from __future__ import annotations

import json

import pytest

from benchmarks.recursive_cases import get_case
from non_exponential_sudoku import (
    CapacityError, ContractionEngine, ContractorConfig, CostLedger,
    LeafConfig, RecursionConfig, simple_network,
)

pytestmark = pytest.mark.checkpoint


def test_exhaustive_leaf_has_exact_assignment_oracle_and_ring_counts() -> None:
    network = simple_network(
        2, [([0, 1], {(0, 0): 1, (1, 1): 1})],
        [([0, 1], {(0, 0): 1, (1, 1): 1})],
    )
    baseline = ContractionEngine(ContractorConfig(2, 9, leaf=LeafConfig(limit=5)))
    ledger = CostLedger()
    audited = ContractionEngine(ContractorConfig(2, 9, leaf=LeafConfig(limit=5)),
                                cost_ledger=ledger)
    assert baseline.contract(network) == audited.contract(network)
    report = ledger.report()
    assert report["frame_tree_reconciled"] is True
    assert report["frames_observed"] == audited.stats.recursive_calls == 1
    assert report["work_totals"]["exhaustive_assignments_enumerated"] == 4
    assert report["work_totals"]["vertex_oracle_calls"] == 6
    assert report["work_totals"]["leaf_calls"] == 1
    assert report["frames"][0]["status"] == "completed"
    assert sum(report["ring_call_totals"].values()) > 0
    assert report["frames"][0]["subtree_ring_method_calls"] == sum(
        report["ring_call_totals"].values())


def test_nested_call_tree_and_factor_budget_reconcile() -> None:
    case = get_case("nested-2wire", "reference")
    ledger = CostLedger()
    engine = ContractionEngine(case.config, cost_ledger=ledger)
    assert engine.contract(case.network)[0] == case.expected
    report = ledger.report()
    assert report["frame_tree_reconciled"] is True
    assert report["frames_observed"] == engine.stats.recursive_calls
    assert report["centers_observed"] > 0
    assert report["work_totals"]["mode_dp_work_units"] == engine.stats.mode_dp_operations
    assert report["work_totals"]["child_networks_constructed"] == engine.stats.child_networks
    assert report["work_totals"]["mode_child_factor_evaluations"] == engine.stats.mode_dp_local_child_evaluations
    assert report["work_totals"]["deformation_evaluations"] == engine.stats.interpolation_evaluations
    assert report["work_totals"]["hermite_centers"] == report["centers_observed"]
    assert any(frame["parent_id"] is not None for frame in report["frames"])
    assert all(center["status"] == "completed" for center in report["centers"])
    roots = [f for f in report["frames"] if f["parent_id"] is None]
    assert len(roots) == 1
    assert roots[0]["subtree_ring_method_calls"] == sum(report["ring_call_totals"].values())


def test_capacity_refusal_is_not_disguised_as_completed() -> None:
    net = simple_network(2, [([0, 1], {(0, 0): 1})],
                         [([0, 1], {(0, 0): 1})])
    from non_exponential_sudoku.runtime.config import RecoveryConfig
    ledger = CostLedger()
    engine = ContractionEngine(ContractorConfig(
        2, 5, schedule="micro", recovery=RecoveryConfig(
            method="jet", max_jet_coordinates=20), micro_active_depth=2),
        cost_ledger=ledger)
    with pytest.raises(CapacityError, match="Nested jet needs"):
        engine.contract(net)
    report = ledger.report()
    assert report["frames"][0]["status"] == "refused"
    assert report["centers"][0]["status"] == "refused"
    assert report["refusals"]
    assert report["worst_case_subexponential_bound_proven"] is False


def test_detail_limit_is_explicit_not_a_silent_accounting_loss() -> None:
    case = get_case("nested-2wire", "reference")
    ledger = CostLedger(max_frames=1, max_centers=1)
    engine = ContractionEngine(case.config, cost_ledger=ledger)
    assert engine.contract(case.network)[0] == case.expected
    report = ledger.report()
    assert report["truncation"]["frames"] > 0
    assert report["truncation"]["centers"] > 0
    assert report["frame_tree_reconciled"] is False
    assert report["detail_complete"] is False
    assert report["work_totals"]["recursive_calls"] == engine.stats.recursive_calls
    assert report["work_totals"]["mode_dp_work_units"] == engine.stats.mode_dp_operations


def test_exhaustive_completion_is_distinguished_from_recursive_contract() -> None:
    net = simple_network(1, [([0], {(0,): 1, (1,): 1})],
                         [([0], {(0,): 1, (1,): 1})])
    ledger = CostLedger()
    engine = ContractionEngine(ContractorConfig(1, 5), cost_ledger=ledger)
    assert engine.contract_complete(net)[0] == 2
    report = ledger.report()
    assert report["frame_tree_reconciled"] is True
    assert report["work_totals"]["exhaustive_completion_calls"] == 1
    assert "recursive_calls" not in report["work_totals"]
    assert report["work_totals"]["exhaustive_assignments_enumerated"] == 2
    assert json.loads(json.dumps(report))["frames"][0]["schedule"] == "exhaustive"


@pytest.mark.requires_native
def test_native_leaf_oracle_calls_are_accounted_without_python_fallback() -> None:
    pytest.importorskip("native_recursive")
    net = simple_network(2,
        [([0, 1], {(0, 0): 1, (1, 1): 1})],
        [([0, 1], {(0, 0): 1, (1, 1): 1})])
    config = ContractorConfig(2, 9, leaf=LeafConfig(strategy="eliminate",limit=5),
                              recursion=RecursionConfig(native_leaf=True))
    ledger = CostLedger()
    engine = ContractionEngine(config,cost_ledger=ledger)
    assert engine.contract(net)[0] == 2
    report = ledger.report()
    assert report["work_totals"]["vertex_oracle_calls"] == 8
    assert report["work_totals"]["leaf_elimination_rows"] > 0
    assert report["opaque_native_calls"]["native_leaf_elimination"] == 1


def test_ring_trace_is_optional_and_does_not_change_results() -> None:
    case = get_case("parity-2wire", "reference")
    normal = ContractionEngine(case.config)
    ledger = CostLedger()
    traced = ContractionEngine(case.config, cost_ledger=ledger)
    assert traced.contract(case.network) == normal.contract(case.network)
    assert traced.stats == normal.stats
    assert ledger.report()["frame_tree_reconciled"] is True


def test_center_detail_truncation_is_reported_even_with_complete_frame_tree() -> None:
    case = get_case("parity-2wire", "reference")
    ledger = CostLedger(max_centers=1)
    assert ContractionEngine(case.config,cost_ledger=ledger).contract(case.network)[0] == case.expected
    report = ledger.report()
    assert report["frame_tree_reconciled"] is True
    assert report["detail_complete"] is False
    assert report["truncation"]["centers"] == 1


def test_native_kernel_calls_are_owned_by_the_active_frame() -> None:
    ledger = CostLedger()
    with ledger.frame(depth=0, wires=2, precision=9, ring_depth=0, schedule="micro"):
        ledger.native("outer_kernel")
        with ledger.frame(depth=1, wires=1, precision=9, ring_depth=1, schedule="micro"):
            ledger.native("inner_kernel")
            ledger.native("inner_kernel")
    report = ledger.report()
    assert report["schema_version"] == "1.1"
    assert report["frame_tree_reconciled"] is True
    assert report["opaque_native_calls"] == {"inner_kernel": 2, "outer_kernel": 1}
    parent, child = report["frames"]
    assert parent["native_calls"] == {"outer_kernel": 1}
    assert child["native_calls"] == {"inner_kernel": 2}
    assert parent["exclusive_native_kernel_calls"] == 1
    assert parent["subtree_native_kernel_calls"] == 3
    assert child["subtree_native_kernel_calls"] == 2

def test_ring_call_counters_store_tuples_and_preserve_json_labels() -> None:
    from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial

    ring = Padic(3, modulus_polynomial(3), 9)
    ledger = CostLedger()
    with ledger.frame(depth=0, wires=1, precision=9,
                      ring_depth=0, schedule="micro"):
        assert ring.mul(ring.one, ring.one) == ring.one
        assert ring.mul(ring.one, ring.one) == ring.one
    assert all(isinstance(key, tuple) for key in ledger.total_ring_calls)
    expected = {"orchestration/Padic.mul/p=9/e=3/q=1/depth=0": 2}
    report = ledger.report()
    assert report["ring_call_totals"] == expected
    assert report["frames"][0]["ring_calls"] == expected
    assert json.loads(json.dumps(report))["ring_call_totals"] == expected
