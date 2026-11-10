"""Adversarial finite witnesses distinguish numeric admission from hardness."""
from __future__ import annotations

import pytest

from non_exponential_sudoku.eth.cnf import count_bruteforce
from non_exponential_sudoku.eth.paper_admitted_witness import (
    virtual_coupled_3cnf_step5,
)
from reference.eth_structural_adversary import (
    affine_three_cnf, cyclic_three_cnf, natural_order_induced_width,
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
