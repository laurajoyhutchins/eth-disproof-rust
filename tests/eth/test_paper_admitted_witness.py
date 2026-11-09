"""Paper/Lean crosswalk: real balancing witness and virtual Step-5 admission.

This test suite deliberately separates a finite balancing lemma instance
from a gargantuan, symbolically described main-body parameter instance.
Neither executes the upstream Lean machine or counts the virtual CNF.
"""
from __future__ import annotations

from dataclasses import asdict
from fractions import Fraction

import pytest

from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.parameters import (
    audit_bounded_cnf, audit_paper_bounds, derive_paper_parameters,
)
from non_exponential_sudoku.eth.paper_admitted_witness import (
    PAPER_COMMIT, LEAN_THEOREM,
    virtual_unit_cnf_step5, concrete_unit_balance_witness,
)


@pytest.mark.checkpoint
def test_virtual_paper_step5_unit_family_admitted_without_allocating_n() -> None:
    # n=2**(2**34). This test may NEVER evaluate 2**lambda as an integer:
    # doing so would consume roughly 2 GiB just to store the dimension.
    report = virtual_unit_cnf_step5(1 << 34)
    assert report.n_description == "2**17179869184"
    assert report.lambda_bits == 17179869184
    assert report.nu_bits == 34
    assert (report.r, report.Q, report.R) == (113, 3947580, 524288)
    assert report.variable_count_binary_bits == 17179869185
    assert report.exact_model_count == 1
    assert report.symbolic_M_equals_n
    assert report.admitted_by_sufficient_conditions
    assert all(check.status == "proved" for check in report.checks)
    assert report.parameters_match_paper_step5
    assert report.materialized_formula is False
    assert report.executed_lean_machine is False
    assert PAPER_COMMIT == "4eaee87548250b2682affda7d05d947c05554bae"
    assert LEAN_THEOREM.endswith(".exact_count_eth")
    assert report.D_expression == "113**7895160"
    assert report.upper_log2_D <= 55266120


@pytest.mark.checkpoint
def test_one_lower_exponent_is_not_admitted_by_paper_sufficient_checks() -> None:
    report = virtual_unit_cnf_step5(1 << 33)
    assert not report.admitted_by_sufficient_conditions
    assert report.check_status("six_R_at_most_Q") == "refuted"


@pytest.mark.checkpoint
def test_symbolic_param_derivation_agrees_with_actual_integer_reference() -> None:
    # λ=2**20 is large but n fits in 128 KiB; this is a *derivation*
    # cross-check, not an admitted asymptotic case.
    L = 1 << 20
    witness = virtual_unit_cnf_step5(L)
    n = 1 << L
    paper = derive_paper_parameters(n)
    assert (witness.lambda_bits, witness.nu_bits, witness.r,
            witness.Q, witness.R) == (
                paper.lambda_bits, paper.nu_bits, paper.r, paper.Q, paper.R)
    assert witness.D_expression == f"{paper.r}**{2 * paper.Q}"
    assert not witness.admitted_by_sufficient_conditions

    exact = audit_paper_bounds(n, n, b=1, w=1)
    outcomes = dict(exact.conditions)
    for check in witness.checks:
        if check.name not in outcomes:
            continue
        if check.status == "proved":
            assert outcomes[check.name], check.name
        if check.status == "refuted":
            assert not outcomes[check.name], check.name


@pytest.mark.checkpoint
def test_virtual_certificate_is_fail_closed_and_has_no_unsafe_fallback() -> None:
    for value in (0, -1, True, 3.14):
        with pytest.raises((ValueError, TypeError)):
            virtual_unit_cnf_step5(value)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="descriptor"):
        virtual_unit_cnf_step5(1 << 34, max_descriptor_bits=16)


@pytest.mark.integration
def test_finite_paper_incidence_balance_has_all_labels_and_group_bounds() -> None:
    # This is an actual, fully enumerated admissible instance of the
    # INCIDENCE BALANCING LEMMA, not of the asymptotic Step-5 schedule.
    n = 4096
    witness = concrete_unit_balance_witness(n)
    assert witness.n == witness.M == n
    assert (witness.r, witness.Q, witness.D) == (2, 2, 16)
    assert witness.max_label_load == 256
    assert witness.max_variable_group == 2048
    assert witness.balancing_lemma_hypotheses
    assert witness.balancing_lemma_conclusions
    assert witness.stronger_overview_balance_hypotheses
    assert len(witness.variable_schedules) == n
    assert len(witness.clause_schedules) == n

    # Independent enumeration of every incidence label and group, not
    # merely trusting the summary counters returned by the witness.
    from collections import Counter

    counts = Counter(zip(witness.variable_schedules, witness.clause_schedules))
    assert len(counts) == witness.D
    assert set(counts.values()) == {n // witness.D}
    for t in range(witness.Q):
        groups = Counter(v[t] for v in witness.variable_schedules)
        assert groups == {0: n // 2, 1: n // 2}

    formula = CNFFormula(n, tuple((i,) for i in range(1, n + 1)))
    assert len(formula.clauses) == n
    assert not audit_bounded_cnf(formula).admitted
    assert witness.paper_step5_admitted is False
    assert witness.executed_full_spectral_construction is False


@pytest.mark.checkpoint
def test_finite_balancing_witness_refuses_invalid_dimensions() -> None:
    for n in (0, 16, 1024, 3071, 4095, 50001):
        with pytest.raises(ValueError):
            concrete_unit_balance_witness(n)


@pytest.mark.integration
def test_source_pinned_evidence_serializes_without_misrepresenting_lean() -> None:
    from benchmarks.eth.paper_admitted_witness import experiment

    report = experiment()
    assert report["status"] == "complete"
    assert report["inputs_stable"] is True
    assert report["virtual_step5"]["admitted_by_sufficient_conditions"] is True
    assert report["finite_balance"]["balancing_lemma_hypotheses"] is True
    assert report["finite_balance"]["paper_step5_admitted"] is False
    assert report["claim_boundary"]["executed_lean_machine"] is False
    assert report["claim_boundary"]["executed_virtual_cnf"] is False
    assert report["source"]["paper_commit"] == PAPER_COMMIT
    assert report["source"]["lean_theorem"] == LEAN_THEOREM
