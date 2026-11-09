"""Executable structural-width witnesses, separate from solver runtimes."""
from __future__ import annotations

from itertools import combinations, permutations
from random import Random

import pytest

from reference.elimination_width import (
    certify_dense_order, forest_leaf_order,
)
from reference.sudoku_frontier_width import (
    audit_cell_order, row_major_width_audit, row_major_width_formula,
)

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize("box,expected", [
    (1, 0), (2, 28), (3, 117), (4, 336), (5, 775), (6, 1548),
])
def test_row_major_exact_frontier_width(box: int, expected: int) -> None:
    audit = row_major_width_audit(box)
    assert audit.max_live_obligation_bits == row_major_width_formula(box) == expected
    if box >= 2:
        assert audit.peak_after_cells == audit.side + 1
        assert audit.half_cut_row_column_units >= audit.side
        assert audit.max_live_obligation_bits >= audit.cells


def test_half_cut_lower_bound_exhaustive_for_four_by_four() -> None:
    # Every subset of 8 processed cells represents the midway cut of
    # some permutation. Checking all 12,870 witnesses is independent of
    # the incremental width auditor.
    n = 4
    for chosen in combinations(range(n*n), n*n//2):
        selected = set(chosen)
        mixed_rows = sum(0 < sum(r*n+c in selected for c in range(n)) < n
                         for r in range(n))
        mixed_cols = sum(0 < sum(r*n+c in selected for r in range(n)) < n
                         for c in range(n))
        assert mixed_rows + mixed_cols >= n


@pytest.mark.parametrize("box", (2, 3, 4))
def test_random_cell_orders_obey_middle_cut_width_lower_bound(box: int) -> None:
    n = box*box
    rng = Random(box)
    cells = list(range(n*n))
    for _ in range(32):
        rng.shuffle(cells)
        audit = audit_cell_order(box, cells)
        assert audit.half_cut_row_column_units >= n
        assert audit.half_cut_obligation_bits >= n*n
        assert audit.max_live_obligation_bits >= n*n


def test_frontier_width_matches_real_blank_four_by_four_statistics() -> None:
    from non_exponential_sudoku.sudoku.three_cnf import Puzzle
    from non_exponential_sudoku.sudoku.frontier import count_frontier
    result = count_frontier(Puzzle(2, (0,) * 16))
    assert result.count == 288
    assert result.stats.max_frontier_bits == row_major_width_formula(2)
    # A structural-bit lower bound is not a lower bound on reachable states.
    assert result.stats.peak_states < 2 ** row_major_width_formula(2)


@pytest.mark.parametrize("bad", (0, -2, True))
def test_invalid_box_orders_rejected(bad: int) -> None:
    with pytest.raises(ValueError):
        row_major_width_audit(bad)


def test_order_permutation_is_validated() -> None:
    with pytest.raises(ValueError):
        audit_cell_order(2, list(range(15)))
    with pytest.raises(ValueError):
        audit_cell_order(2, [0] * 16)


def test_constructed_chain_order_bounds_dense_slots_for_all_lengths() -> None:
    for groups in (1, 2, 3, 8, 32, 64):
        factors = tuple((i, i+1) for i in range(groups-1))
        domains = (4,) * groups  # two Boolean variables per group
        order = forest_leaf_order(factors, domains)
        cert = certify_dense_order(factors, domains, order)
        assert cert.order == tuple(range(groups))
        assert cert.max_joined_variables <= 2
        assert cert.max_joined_entries <= 16
        assert cert.max_output_entries <= 4
        assert cert.joined_assignments_upper <= 16 * groups


def test_forest_constructor_handles_branching_and_rejects_cycles() -> None:
    factors = tuple((0, i) for i in range(1, 17))
    order = forest_leaf_order(factors, (2,) * 17)
    cert = certify_dense_order(factors, (2,) * 17, order)
    assert cert.max_joined_variables == 2
    assert cert.max_joined_entries == 4
    assert set(order) == set(range(17))
    # The center may be chosen before the final remaining leaf when both
    # have degree one; either order retains width two.
    for bad in ([(0, 1), (1, 2), (2, 0)], [(0, 1, 2)]):
        with pytest.raises(ValueError):
            forest_leaf_order(bad, (2, 2, 2))


def test_clique_has_large_joined_scope_for_every_order() -> None:
    # This is a dense-factor *representation* obstruction. It does
    # not establish a universal exact-counting runtime lower bound.
    factors = tuple(combinations(range(4), 2))
    factors = tuple(factors)
    for order in permutations(range(4)):
        cert = certify_dense_order(factors, (2,) * 4, order)
        assert cert.max_joined_variables == 4
        assert cert.max_joined_entries == 16
        assert cert.max_output_entries == 8


def test_variable_domain_and_order_validation() -> None:
    with pytest.raises(ValueError):
        certify_dense_order([(0, 2)], (2, 2), (0, 1))
    with pytest.raises(ValueError):
        certify_dense_order([(0, 1)], (2, 0), (0, 1))
    with pytest.raises(ValueError):
        certify_dense_order([(0, 1)], (2, 2), (0, 0))
    with pytest.raises(ValueError):
        forest_leaf_order([(0, 0)], (2,))
