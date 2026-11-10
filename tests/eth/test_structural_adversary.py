"""Adversarial finite witnesses distinguish numeric admission from hardness."""
from __future__ import annotations

import pytest

from non_exponential_sudoku.eth.cnf import count_bruteforce
from non_exponential_sudoku.eth.paper_admitted_witness import (
    virtual_coupled_3cnf_step5,
)
from reference.eth_structural_adversary import (
    affine_three_cnf, cyclic_three_cnf, natural_order_induced_width,
    subcubic_grid_cnf, certify_subcubic_grid_minor,
    virtual_subcubic_grid_step5,
)


@pytest.mark.checkpoint
@pytest.mark.parametrize(("n", "affine_width"), (
    (8, 6), (16, 10), (32, 17), (64, 34),
))
def test_equal_bounded_incidence_profiles_differ_in_natural_order_width(
    n: int, affine_width: int,
) -> None:
    easy = natural_order_induced_width(cyclic_three_cnf(n))
    adversary = natural_order_induced_width(affine_three_cnf(n))
    for profile in (easy, adversary):
        assert profile.variables == n
        assert profile.clauses == n
        assert profile.literal_occurrences == 3 * n
        assert profile.maximum_clause_width == 3
        assert profile.maximum_variable_occurrences == 3
    # Explicit elimination proves an UPPER bound of 4 on the easy family.
    assert easy.natural_order_induced_width == 4
    # This is width of ONE ordering, NEVER a graph treewidth lower bound.
    assert adversary.natural_order_induced_width == affine_width


@pytest.mark.checkpoint
def test_small_affine_count_is_real_not_a_symbolic_surrogate() -> None:
    formula = affine_three_cnf(8)
    assert len(formula.clauses) == 8
    count = count_bruteforce(formula)
    assert 0 <= count <= 1 << formula.nvars
    # The exact result is available only for the finite oracle fixture.
    assert count == sum(formula.satisfied_mask(mask)
                        for mask in range(1 << formula.nvars))


@pytest.mark.integration
def test_structural_growth_probe_is_not_placed_in_checkpoint() -> None:
    n = 128
    easy = natural_order_induced_width(cyclic_three_cnf(n))
    adversarial = natural_order_induced_width(affine_three_cnf(n))
    assert easy.natural_order_induced_width == 4
    assert adversarial.natural_order_induced_width == 52


@pytest.mark.checkpoint
def test_virtual_step5_numeric_admission_does_not_certify_graph_hardness() -> None:
    # Both families have n distinct clauses, three literals each, three
    # variable occurrences each. Thus their symbolic M,b,w inputs to
    # the Step-5 numeric sufficient conditions agree. The preexisting
    # report documents the *cyclic* family only.
    witness = virtual_coupled_3cnf_step5(1 << 34)
    assert witness.admitted_by_sufficient_conditions
    assert witness.M_description == "3*(2**17179869184)"
    assert not witness.executed_paper_algorithm
    assert not witness.executed_lean_machine
    # The finite affine profile, not a virtual enormous graph, is tested.
    finite = natural_order_induced_width(affine_three_cnf(16))
    assert finite.maximum_variable_occurrences == 3
    assert finite.maximum_clause_width == 3


@pytest.mark.checkpoint
@pytest.mark.parametrize("n", (0, 7, 12, 1024, True))
def test_structural_probe_rejects_invalid_materialization(n: int) -> None:
    with pytest.raises(ValueError):
        cyclic_three_cnf(n)
    with pytest.raises(ValueError):
        affine_three_cnf(n)


@pytest.mark.checkpoint
@pytest.mark.parametrize("side", (2, 4, 8))
def test_subcubic_wall_has_independently_checked_grid_minor(side: int) -> None:
    formula = subcubic_grid_cnf(side)
    certificate = certify_subcubic_grid_minor(formula, side=side)
    assert certificate.variables == 4 * side * side
    assert certificate.clauses == 6 * side * side - 2 * side
    assert certificate.literal_occurrences == 12 * side * side - 4 * side
    assert certificate.maximum_occurrences == 3
    assert certificate.maximum_clause_width == 2
    assert certificate.contracted_grid_edges == 2 * side * (side - 1)
    # Every grid row/column cross meets every other one. Any <side
    # vertices miss an entire row and an entire column, so the cross
    # bramble has order >=side; the grid's treewidth is >=side-1.
    assert certificate.treewidth_lower_bound == side - 1
    assert certificate.variables <= certificate.literal_occurrences <= (
        3 * certificate.variables
    )


@pytest.mark.integration
def test_larger_subcubic_wall_retains_growing_grid_minor() -> None:
    side = 16
    certificate = certify_subcubic_grid_minor(
        subcubic_grid_cnf(side), side=side,
    )
    assert certificate.variables == 1024
    assert certificate.treewidth_lower_bound == 15


@pytest.mark.checkpoint
def test_grid_minor_verifier_rejects_missing_edge_and_invalid_side() -> None:
    from non_exponential_sudoku.eth.cnf import CNFFormula
    original = subcubic_grid_cnf(2)
    truncated = CNFFormula(original.nvars, original.clauses[:-1])
    with pytest.raises(ValueError, match="clauses differ"):
        certify_subcubic_grid_minor(truncated, side=2)
    for side in (0, 1, 3, 32, True):
        with pytest.raises(ValueError):
            subcubic_grid_cnf(side)


@pytest.mark.checkpoint
def test_virtual_grid_minor_numeric_admission_and_proven_tw_growth() -> None:
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
def test_virtual_grid_minor_admission_refuses_absent_source_premises() -> None:
    for lam in (0, 1, 3, 10, 1 << 20, (1 << 34) - 1, True):
        with pytest.raises(ValueError):
            virtual_subcubic_grid_step5(lam)
