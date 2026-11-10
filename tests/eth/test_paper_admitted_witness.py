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
    virtual_unit_cnf_step5, virtual_coupled_3cnf_step5,
    concrete_unit_balance_witness,
    unit_copy_partition,
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


@pytest.mark.checkpoint
def test_coupled_cyclic_three_cnf_satisfies_full_symbolic_paper_step5() -> None:
    # This is NOT the trivial AND-of-independent-unit-clauses witness.
    # It is the connected family AND_i(x_i OR x_(i+1) OR x_(i+2)),
    # with n=2**(2**34). No enormous integer n or formula is allocated.
    coupled = virtual_coupled_3cnf_step5(1 << 34)
    unit = virtual_unit_cnf_step5(1 << 34)
    assert coupled.n_description == "2**17179869184"
    assert coupled.M_description == "3*(2**17179869184)"
    assert (coupled.r, coupled.Q, coupled.R) == (113, 3947580, 524288)
    assert coupled.admitted_by_sufficient_conditions
    assert all(check.status == "proved" for check in coupled.checks)
    assert coupled.check_status("balancing_incidence_inequality") == (
        unit.check_status("balancing_incidence_inequality")
    )
    assert coupled.check_status("stronger_overview_12_D_squared_le_M") == "proved"
    assert not coupled.materialized_formula
    assert not coupled.executed_paper_algorithm
    assert not coupled.executed_lean_machine


@pytest.mark.checkpoint
def test_coupled_virtual_certificate_matches_exact_paper_admission_abi() -> None:
    # Representable dimensions; still *not* literal Step-5 admitted.
    lam = 1 << 20
    n = 1 << lam
    expected = virtual_coupled_3cnf_step5(lam)
    actual = audit_paper_bounds(n, 3 * n, b=3, w=3)
    outcomes = dict(actual.conditions)
    for check in expected.checks:
        if check.name not in outcomes:
            continue
        if check.status == "proved":
            assert outcomes[check.name], check.name
        elif check.status == "refuted":
            assert not outcomes[check.name], check.name
    assert not expected.admitted_by_sufficient_conditions
    assert not actual.admitted


@pytest.mark.checkpoint
def test_finite_cyclic_three_cnf_is_coupled_and_normalizes_as_proved() -> None:
    # A genuinely connected 3-regular incidence structure, not an
    # independent-unit formula and not a paper-admitted finite instance.
    for n in (8, 16):
        clauses = tuple(
            (i + 1, (i + 1) % n + 1, (i + 2) % n + 1)
            for i in range(n)
        )
        formula = CNFFormula(n, clauses)
        assert len(formula.clauses) == n
        assert all(len(clause) == 3 for clause in formula.clauses)
        counts = [sum(var in clause for clause in formula.clauses)
                  for var in range(1, n + 1)]
        assert set(counts) == {3}
        paper = audit_bounded_cnf(formula)
        assert paper.M == 3 * n
        assert paper.max_variable_occurrences == paper.max_clause_width == 3
        assert not paper.admitted


@pytest.mark.checkpoint
def test_coupled_virtual_certificate_refuses_invalid_descriptors() -> None:
    for value in (0, -1, True, 3.14):
        with pytest.raises((ValueError, TypeError)):
            virtual_coupled_3cnf_step5(value)  # type: ignore[arg-type]


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
    assert report["virtual_coupled_step5"]["admitted_by_sufficient_conditions"] is True
    assert report["virtual_coupled_step5"]["global_intermediate_size_bound_proved"] is False
    assert report["virtual_coupled_step5"]["physical_formula_materialized"] is False
    assert report["virtual_coupled_step5"]["executed_lean_machine"] is False
    assert report["finite_balance"]["balancing_lemma_hypotheses"] is True
    assert report["finite_balance"]["paper_step5_admitted"] is False
    assert report["claim_boundary"]["executed_lean_machine"] is False
    assert report["claim_boundary"]["executed_virtual_cnf"] is False
    assert report["source"]["paper_commit"] == PAPER_COMMIT
    assert report["source"]["lean_theorem"] == LEAN_THEOREM
    assert report["finite_copy_partition"]["copy_count"] == 256
    assert report["finite_copy_partition"]["max_copy_variables"] == 16
    assert report["finite_copy_partition"]["rank_upper_all_rational_centers"] == 256
    assert report["finite_copy_partition"]["rank_upper_for_taylor_coefficient_order_2"] == 768
    assert report["finite_copy_partition"]["full_spectral_tensor_constructed"] is False


@pytest.mark.integration
def test_unit_clause_copy_partition_proves_small_uniform_tensor_rank() -> None:
    balance = concrete_unit_balance_witness(4096)
    copies = unit_copy_partition(balance)
    assert copies.copy_count == 256
    assert copies.max_copy_variables == 16
    assert copies.max_copy_variables <= balance.D
    assert copies.rank_upper_all_centers == 256
    assert copies.taylor_coefficient_rank_upper(2) == 768
    assert len(copies.variable_to_copy) == balance.n
    assert len(copies.copy_blocks) == copies.copy_count
    assert sorted(v for block in copies.copy_blocks for v in block) == list(range(balance.n))
    for block in copies.copy_blocks:
        assert len(block) == 16
        labels = {
            tuple((balance.variable_schedules[v][t],
                   balance.clause_schedules[v][t]) for t in range(balance.Q))
            for v in block
        }
        assert len(labels) == len(block)


@pytest.mark.integration
def test_actual_spectral_step4_rows_are_local_to_auxiliary_copy() -> None:
    # Small structural witness: invoke the real spectral projector and
    # transfer path, then independently inspect *every* nonzero row
    # coefficient. No truth-table enumeration or paper admission claim.
    from non_exponential_sudoku.eth.construction import (
        construct_from_schedules, construct_implicit_auxiliary,
    )
    from non_exponential_sudoku.eth.support_rank import (
        uniform_support_profile,
    )

    n = 32
    formula = CNFFormula(n, tuple((v + 1,) for v in range(n)))
    variable = tuple(((v & 1), ((v >> 1) & 1)) for v in range(n))
    clause = tuple((((v >> 2) & 1), ((v >> 3) & 1)) for v in range(n))
    aux = construct_implicit_auxiliary(
        r=2, Q=2, R=2, measurement_basis="projector",
    )
    constructed = construct_from_schedules(formula, aux, variable, clause)
    # Copy index is the count of preceding occurrences of the same label.
    label_counts: dict[tuple[tuple[int, int], ...], int] = {}
    blocks: list[list[int]] = []
    for v in range(n):
        label = tuple((variable[v][t], clause[v][t]) for t in range(2))
        copy = label_counts.get(label, 0)
        label_counts[label] = copy + 1
        if len(blocks) <= copy:
            blocks.append([])
        blocks[copy].append(v)
    assert len(blocks) == 2
    for v, forms in enumerate(constructed.replacements.clauses):
        label = tuple((variable[v][t], clause[v][t]) for t in range(2))
        # Among occurrences of this label, variable v is assigned the
        # same copy number by construct_from_schedules.
        copy = blocks.index(next(block for block in blocks if v in block))
        allowed = set(blocks[copy])
        assert len(forms) == 1
        support = {i for i, p in enumerate(forms[0].coefficients)
                   if any(p.coefficients)}
        assert support <= allowed
    order = tuple(v for block in blocks for v in block)
    profile = uniform_support_profile(
        formula, constructed.replacements, variable_order=order,
    )
    assert max(cut.rank_upper for cut in profile) <= 256
    assert profile[15].rank_upper == 1  # exact boundary between copies
