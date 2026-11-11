"""Finite CNF fixture contracts, not ETH hardness benchmarks.

Each assertion has a bounded interpretation: incidence counts, positivity,
one elimination order, or a verified grid minor. No treewidth *lower* bound
is inferred from a chosen elimination order.
"""
from __future__ import annotations

from collections import Counter

import pytest

from non_exponential_sudoku.eth import CNFFormula, count_bruteforce
from non_exponential_sudoku.eth.parameters import audit_bounded_cnf
from reference.eth_bounded_incidence_fixtures import (
    affine_three_cnf, alternating_signs, certify_subcubic_grid_minor,
    cyclic_three_cnf, natural_order_induced_width, subcubic_grid_cnf,
)


@pytest.mark.checkpoint
@pytest.mark.parametrize(("n", "affine_order_width"), (
    (8, 6), (16, 10), (32, 17), (64, 34),
))
def test_equal_incidence_bounds_do_not_fix_chosen_elimination_width(
    n: int, affine_order_width: int,
) -> None:
    cyclic = cyclic_three_cnf(n)
    affine = affine_three_cnf(n)
    for formula in (cyclic, affine):
        profile = natural_order_induced_width(formula)
        assert profile.variables == n
        assert profile.clauses == n
        assert profile.literal_occurrences == 3 * n
        assert profile.maximum_clause_width == 3
        assert profile.maximum_variable_occurrences == 3
        assert formula.satisfied_mask((1 << n) - 1)
        # This family cannot test SAT decision hardness: all literals positive.
    assert natural_order_induced_width(cyclic).natural_order_induced_width == 4
    assert (natural_order_induced_width(affine).natural_order_induced_width
            == affine_order_width)
    # The affine result is an order-specific UPPER bound, not a proof
    # that all possible elimination orders are wide.


@pytest.mark.integration
def test_larger_affine_order_trace_does_not_claim_treewidth_lower_bound() -> None:
    assert natural_order_induced_width(cyclic_three_cnf(128)).natural_order_induced_width == 4
    assert natural_order_induced_width(affine_three_cnf(128)).natural_order_induced_width == 52


@pytest.mark.checkpoint
@pytest.mark.parametrize("n", (0, 7, 12, 1024, True))
def test_finite_fixture_dimension_caps_are_explicit(n: int) -> None:
    for constructor in (cyclic_three_cnf, affine_three_cnf):
        with pytest.raises(ValueError):
            constructor(n)


@pytest.mark.checkpoint
@pytest.mark.parametrize("side", (2, 4, 8))
def test_grid_port_edges_verify_a_square_grid_minor_not_hardness(side: int) -> None:
    formula = subcubic_grid_cnf(side)
    receipt = certify_subcubic_grid_minor(formula, side=side)
    assert receipt.variables == 4 * side * side
    assert receipt.clauses == 6 * side * side - 2 * side
    assert receipt.literal_occurrences == 12 * side * side - 4 * side
    assert receipt.maximum_occurrences == 3
    assert receipt.maximum_clause_width == 2
    assert receipt.contracted_grid_edges == 2 * side * (side - 1)
    # Contracting port cycles gives a square-grid minor, and the
    # grid-cross bramble has order >=side. Hence tw>=side-1.
    assert receipt.treewidth_lower_bound == side - 1
    assert formula.satisfied_mask((1 << formula.nvars) - 1)
    # Both the treewidth claim and all-true satisfaction can hold.


@pytest.mark.integration
def test_larger_finite_grid_minor_without_exponential_counting() -> None:
    receipt = certify_subcubic_grid_minor(subcubic_grid_cnf(16), side=16)
    assert receipt.variables == 1024
    assert receipt.treewidth_lower_bound == 15


@pytest.mark.checkpoint
def test_grid_minor_contract_rejects_missing_edge_and_bad_dimensions() -> None:
    original = subcubic_grid_cnf(2)
    corrupted = CNFFormula(original.nvars, original.clauses[:-1])
    with pytest.raises(ValueError, match="clauses differ"):
        certify_subcubic_grid_minor(corrupted, side=2)
    for side in (0, 1, 3, 32, True):
        with pytest.raises(ValueError):
            subcubic_grid_cnf(side)


@pytest.mark.integration
def test_literal_signs_change_count_without_changing_graph_or_incidence() -> None:
    positive = subcubic_grid_cnf(2)
    signed = alternating_signs(positive)
    assert all(literal > 0 for clause in positive.clauses for literal in clause)
    assert any(literal < 0 for clause in signed.clauses for literal in clause)
    assert not signed.satisfied_mask((1 << signed.nvars) - 1)

    def unsigned_edges(formula: CNFFormula) -> set[frozenset[int]]:
        return {
            frozenset(abs(v) for v in clause)
            for clause in formula.clauses
        }

    assert unsigned_edges(signed) == unsigned_edges(positive)
    for formula in (positive, signed):
        audit = audit_bounded_cnf(formula)
        assert audit.max_variable_occurrences == 3
        assert audit.max_clause_width == 2
        assert audit.M == 2 * len(formula.clauses)
        assert not audit.admitted  # Small concrete n fails paper Step 5.
        assert max(Counter(abs(v) for c in formula.clauses for v in c).values()) == 3

    assert count_bruteforce(positive) == 1649
    assert count_bruteforce(signed) == 147
    # These finite model counts are correctness fixtures, not hard cases.
