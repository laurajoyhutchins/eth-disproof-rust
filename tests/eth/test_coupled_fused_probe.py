"""Falsify generic compact fused tables without mistaking finite data for ETH.

The coupled families share n clauses, three literals/variable, and
polynomial-size input.  The paper parameters are *not* executable at
these finite n.  The structural oracle follows the source's greedy
scope heuristic, while an independent transfer matrix checks the
cyclic family's exact first Taylor jet.
"""
from __future__ import annotations

from fractions import Fraction

import pytest

from benchmarks.eth.coupled_fused_probe import (
    brute_force_center_jet, coupled_deformation, coupled_formula,
    cyclic_transfer_jet, fused_scope_audit, run_case,
)
from non_exponential_sudoku.eth.design import certify_measurements
from non_exponential_sudoku.runtime.budget import CapacityError


@pytest.mark.checkpoint
@pytest.mark.parametrize("kind", ["cyclic", "shuffled"])
@pytest.mark.parametrize("n", [8, 10])
def test_real_coupled_incidence_and_manual_measurement_certificate(
    kind: str, n: int,
) -> None:
    formula = coupled_formula(n, kind)  # type: ignore[arg-type]
    design, replacements = coupled_deformation(formula)
    assert len(formula.clauses) == n
    assert {len(clause) for clause in formula.clauses} == {3}
    assert {sum(var in clause for clause in formula.clauses)
            for var in range(1, n + 1)} == {3}
    certificate = certify_measurements(
        formula, replacements, design, at=Fraction(1)
    )
    assert certificate.total_measurements == 0
    assert len(certificate.occurrences) == n
    assert design.tau == 0  # An admitted paper design is NOT asserted.


@pytest.mark.checkpoint
@pytest.mark.parametrize("n", [8, 10])
def test_independent_cyclic_transfer_matches_full_boolean_cube(n: int) -> None:
    formula = coupled_formula(n, "cyclic")
    for center in (Fraction(0), Fraction(1)):
        assert cyclic_transfer_jet(n, center) == brute_force_center_jet(formula, center)


@pytest.mark.checkpoint
@pytest.mark.parametrize("kind", ["cyclic", "shuffled"])
def test_actual_fused_execution_matches_exact_independent_oracles(
    kind: str,
) -> None:
    result = run_case(8, kind)  # type: ignore[arg-type]
    assert result["status"] == "exact"
    assert result["independent_full_cube"] is True
    if kind == "cyclic":
        assert result["independent_four_state_transfer"] is True
    scope = result["scope"]
    stats = result["stats"]
    assert isinstance(scope, dict) and isinstance(stats, dict)
    assert stats["factor_scope_basis"] == "variables"
    assert stats["factor_scope_peak"] == scope["max_joined_scope"]
    assert stats["factor_assignments_tested"] == scope["total_charged_assignment_slots"]
    assert stats["jet_operations"] > 0
    assert stats["max_coefficient_bits"] > 0


@pytest.mark.checkpoint
def test_fused_cyclic_scopes_remain_bounded_but_not_by_naive_board_size() -> None:
    for n in (8, 16, 32):
        formula = coupled_formula(n, "cyclic")
        _, replacements = coupled_deformation(formula)
        audit = fused_scope_audit(formula, replacements, family="cyclic")
        assert audit.max_initial_scope == 3
        assert audit.max_joined_scope == 5
        assert audit.max_dense_joined_entries == 32
        assert len(audit.order) == n
        assert sorted(audit.order) == list(range(n))


@pytest.mark.integration
def test_fused_structural_obstruction_is_coupling_dependent() -> None:
    # A verified finite family of bounded-degree interactions. No proof
    # of linear induced width for an infinite expander family is claimed.
    expected = {32: 14, 64: 27, 128: 54}
    for n, joined_width in expected.items():
        formula = coupled_formula(n, "shuffled")
        _, replacements = coupled_deformation(formula)
        audit = fused_scope_audit(formula, replacements, family="shuffled")
        assert audit.max_initial_scope == 3
        assert audit.max_joined_scope == joined_width
        assert audit.max_dense_joined_entries == 1 << joined_width
        assert audit.total_charged_assignment_slots >= audit.max_dense_joined_entries
        assert audit.max_dense_joined_entries > 32
    # Source geometry, not a lower bound for symbolic exact counting.


@pytest.mark.integration
def test_actual_fused_refusal_matches_uncapped_scope_prediction() -> None:
    refused = run_case(32, "shuffled", max_factor_entries=1024)
    assert refused["status"] == "capacity_refusal"
    assert "factor entry limit" in str(refused["reason"])
    scope = refused["scope"]
    assert isinstance(scope, dict)
    assert scope["max_joined_scope"] == 14
    assert scope["max_dense_joined_entries"] == 1 << 14
    # In contrast a 32-variable cyclic instance keeps width 5.
    easy = run_case(32, "cyclic", max_factor_entries=1024)
    assert easy["status"] == "exact"
    assert easy["independent_four_state_transfer"] is True


@pytest.mark.integration
def test_real_fused_nontrivial_first_derivative_agrees_at_twelve_variables() -> None:
    for kind in ("cyclic", "shuffled"):
        result = run_case(12, kind)  # type: ignore[arg-type]
        assert result["status"] == "exact"
        assert result["independent_full_cube"] is True
        coefficients = result["coefficients"]
        assert isinstance(coefficients, tuple)
        assert Fraction(coefficients[1]) != 0


@pytest.mark.checkpoint
def test_guards_keep_unbounded_oracles_and_invalid_families_separate() -> None:
    for kind in ("cyclic", "shuffled"):
        with pytest.raises(CapacityError, match="twelve"):
            brute_force_center_jet(coupled_formula(13, kind))  # type: ignore[arg-type]
    for n in (0, 1, 7, True):
        with pytest.raises(ValueError):
            coupled_formula(n, "cyclic")
    with pytest.raises(ValueError, match="unknown"):
        coupled_formula(8, "unsupported")  # type: ignore[arg-type]
