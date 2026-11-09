"""Positive validation tests of intentionally RED complete-theorem conditions."""
from __future__ import annotations

import pytest

from reference.complete_theorem_gate import (
    CompleteTheoremStatus, IncompleteTheorem, current_theorem_status,
)

pytestmark = pytest.mark.checkpoint


def test_fake_complete_local_numbers_cannot_certify_theorem() -> None:
    # This models arbitrary positive values filled into every LocalBitBound
    # slot. Those values do NOT discharge source totality or input reduction.
    report = current_theorem_status(local_bit_work_gap=None)
    assert report.local_bit_work_gap is None
    assert report.source_and_totality_gaps
    assert report.parameter_transfer_gap is not None
    with pytest.raises(IncompleteTheorem, match='resource_limits_do_not_refuse'):
        report.require_complete()


def test_missing_local_costs_and_other_blockers_are_reported_together() -> None:
    report = current_theorem_status(
        local_bit_work_gap='missing recursive_packet_entry_oracles',
    )
    assert any('recursive_packet_entry_oracles' in x for x in report.outstanding)
    assert any('source_or_totality' in x for x in report.outstanding)
    assert any('cell_parameter' in x for x in report.outstanding)


def test_network_target_does_not_silently_claim_sudoku_cell_result() -> None:
    report = current_theorem_status(local_bit_work_gap=None, target='network')
    assert report.parameter_transfer_gap is None
    assert report.source_and_totality_gaps
    with pytest.raises(IncompleteTheorem):
        report.require_complete()


def test_complete_gate_accepts_structurally_empty_evidence_but_not_in_current_repo() -> None:
    # This tests the mechanical gate only. A hand-constructed status is not
    # evidence that the upstream source actually met these obligations.
    fake = CompleteTheoremStatus('network', None, (), None)
    fake.require_complete()
    actual = current_theorem_status(local_bit_work_gap=None, target='network')
    assert actual != fake
    assert actual.outstanding


def test_unknown_target_refused() -> None:
    with pytest.raises(ValueError):
        current_theorem_status(local_bit_work_gap=None, target='runtime')  # type: ignore[arg-type]
