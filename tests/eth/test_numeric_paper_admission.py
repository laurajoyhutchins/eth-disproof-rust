"""Paper Step-5 NUMERIC admission, never a hardness or runtime certificate.

Virtual certificates prove inequalities for exponent descriptors without
materializing giant CNFs. Finite CNFs check b,w,M with the real normalizer.
No test here asserts that the uncapped algorithm executes or refutes ETH.
"""
from __future__ import annotations

import pytest

from non_exponential_sudoku.eth.paper_admitted_witness import (
    virtual_coupled_3cnf_step5,
)
from non_exponential_sudoku.eth.parameters import audit_bounded_cnf
from reference.eth_bounded_incidence_fixtures import (
    affine_three_cnf, cyclic_three_cnf, subcubic_grid_cnf,
    virtual_subcubic_grid_step5,
)


@pytest.mark.checkpoint
def test_two_numeric_families_have_distinct_graphs_but_same_incidence_premises() -> None:
    for n in (8, 16, 32):
        cyclic = audit_bounded_cnf(cyclic_three_cnf(n))
        affine = audit_bounded_cnf(affine_three_cnf(n))
        assert cyclic.M == affine.M == 3 * n
        assert cyclic.max_variable_occurrences == affine.max_variable_occurrences == 3
        assert cyclic.max_clause_width == affine.max_clause_width == 3
        assert not cyclic.admitted and not affine.admitted
        # Matching numeric premises does not imply matching graph structure,
        # counting complexity, proof execution, or Lean refinement.


@pytest.mark.checkpoint
def test_coupled_virtual_admission_is_only_a_symbolic_inequality_certificate() -> None:
    witness = virtual_coupled_3cnf_step5(1 << 34)
    assert witness.admitted_by_sufficient_conditions
    assert witness.M_description == "3*(2**17179869184)"
    assert not witness.materialized_formula
    assert not witness.executed_paper_algorithm
    assert not witness.executed_lean_machine


@pytest.mark.checkpoint
def test_grid_minor_virtual_step5_checks_symbolic_incidence_margin_only() -> None:
    lam = 1 << 34
    witness = virtual_subcubic_grid_step5(lam)
    assert (witness.r, witness.Q, witness.R) == (113, 3947580, 524288)
    assert witness.numeric_step5_admitted
    assert witness.spectral_overview_margin_proved
    assert witness.spectral_dimension_squared_log2_upper == 4 * 3947580 * 7
    assert witness.spectral_dimension_squared_log2_upper < lam - 3
    assert witness.grid_side_expression == f"2**{(lam - 2) // 2}"
    assert witness.treewidth_lower_bound_expression == (
        f"(2**{(lam - 2) // 2})-1"
    )
    assert not witness.materialized_cnf
    assert not witness.executed_paper_algorithm
    assert not witness.executed_lean_machine


@pytest.mark.checkpoint
def test_real_finite_grid_port_incidence_agrees_with_symbolic_formulas() -> None:
    for side in (2, 4, 8):
        formula = subcubic_grid_cnf(side)
        audit = audit_bounded_cnf(formula)
        assert audit.M == (3 * formula.nvars - 4 * side)
        assert audit.M == 12 * side * side - 4 * side
        assert audit.max_variable_occurrences == 3
        assert audit.max_clause_width == 2
        assert not audit.admitted


@pytest.mark.checkpoint
def test_virtual_grid_numeric_certification_rejects_missing_premises() -> None:
    for lam in (0, 1, 3, 10, 1 << 20, (1 << 34) - 1, True):
        with pytest.raises(ValueError):
            virtual_subcubic_grid_step5(lam)
