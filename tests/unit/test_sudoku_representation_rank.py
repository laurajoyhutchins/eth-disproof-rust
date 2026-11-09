"""TDD for exact Sudoku unit rank and lifted-packet width barriers.

The rank statement concerns valid-digit restrictions. In the canonical
Sudoku tensor, unit oracles alone accept out-of-range distinct bit codes;
the cell oracles exclude them. Never silently change that source ABI.
"""
from __future__ import annotations

from itertools import product
from math import comb

import pytest

from non_exponential_sudoku import Padic, modulus_polynomial
from non_exponential_sudoku.sudoku.input_oracles import CellEntryOracle, UnitEntryOracle
from reference.sudoku_unit_rank import (
    projected_all_different, subset_factor_entry, unit_subset_rank,
    subset_identity_witness,
)
from benchmarks.sudoku_representation_audit import audit_sudoku_representation


def _bitstring(values: tuple[int, ...], width: int) -> tuple[int, ...]:
    return tuple((v >> bit) & 1 for v in values for bit in range(width))


@pytest.mark.checkpoint
def test_exact_subset_decomposition_for_every_four_digit_assignment() -> None:
    for values in product(range(4), repeat=4):
        digits = tuple(values)
        assert subset_factor_entry(4, 2, digits) == projected_all_different(4, digits)
    assert unit_subset_rank(4, 2) == 6
    assert unit_subset_rank(9, 4) == comb(9, 4) == 126
    assert unit_subset_rank(16, 8) == comb(16, 8) == 12870


@pytest.mark.checkpoint
def test_full_small_unit_boolean_matrix_has_predicted_gf2_rank() -> None:
    ring = Padic(5, modulus_polynomial(5), 7)
    oracle = UnitEntryOracle(4, 2)
    assignments = tuple(product(range(4), repeat=2))
    rows = []
    for left in assignments:
        bits = 0
        for j, right in enumerate(assignments):
            answer = oracle(_bitstring(left + right, 2), ring)
            assert answer in (ring.zero, ring.one)
            if answer == ring.one:
                bits |= 1 << j
        rows.append(bits)
    basis: dict[int, int] = {}
    for vector in rows:
        while vector:
            top = vector.bit_length()-1
            if top not in basis:
                basis[top] = vector
                break
            vector ^= basis[top]
    assert len(basis) == unit_subset_rank(4, 2) == 6


@pytest.mark.checkpoint
def test_complement_witness_is_identity_without_dense_matrix() -> None:
    for n, k in ((4, 2), (9, 4), (16, 8)):
        for prefix, suffix in subset_identity_witness(n, k, limit=12):
            assert subset_factor_entry(n, k, prefix + suffix) == 1
            if len(prefix) >= 2:
                broken = prefix[:-1] + (prefix[0],) + suffix
                assert subset_factor_entry(n, k, broken) == 0


@pytest.mark.checkpoint
def test_raw_unit_accepts_invalid_digit_but_cell_guards_it() -> None:
    ring = Padic(5, modulus_polynomial(5), 7)
    raw = UnitEntryOracle(9, 4)
    invalid = (9,) + tuple(range(8))
    assert raw(_bitstring(invalid, 4), ring) == ring.one
    assert projected_all_different(9, invalid) == 0
    assert subset_factor_entry(9, 4, invalid) == 0
    assert CellEntryOracle(9, 4, 0)(
        _bitstring((9, 9, 9), 4), ring) == ring.zero


@pytest.mark.checkpoint
def test_sudoku_width_floor_and_unit_rank_grow() -> None:
    for box, expected_bits, unit_arity, rank in (
        (2, 96, 8, 6), (3, 972, 36, 126), (4, 3072, 64, 12870),
    ):
        row = audit_sudoku_representation(box, with_packing=False)
        assert row["original_boolean_wires"] == expected_bits
        assert row["unit_arity_bits"] == unit_arity
        assert row["min_input_factor_width"] >= unit_arity
        assert row["projected_unit_cut_rank"] == rank
        assert row["raw_unit_rank_lower_bound"] == rank
        assert row["dense_unit_table_entries"] == (1 << unit_arity)
        # This is only a NECESSARY input-table condition, not an
        # assertion about subsequent elimination width or memory.
        assert row["unit_input_arity_le_default_width"] is (unit_arity <= 16)


@pytest.mark.integration
def test_real_sudoku_packet_packing_profiles_without_mode_tables() -> None:
    for box in (2, 3, 4):
        row = audit_sudoku_representation(box, with_packing=True)
        assert row["packing_geometry_valid"]
        assert row["packet_count"] > 0
        assert 1 <= row["max_packet_occupied"] <= 4
        assert row["mode_center_descriptor_count"] >= 0
        assert row["mode_weighted_tuple_lower_log2"] >= 0
        assert row["min_input_factor_width"] >= row["unit_arity_bits"]


@pytest.mark.checkpoint
def test_clues_change_oracles_not_raw_tensor_topology() -> None:
    empty = audit_sudoku_representation(3, with_packing=False, case="empty")
    hard = audit_sudoku_representation(3, with_packing=False, case="hard")
    assert empty["givens"] == 0
    assert hard["givens"] > 0
    for key in ("original_boolean_wires", "unit_arity_bits",
                "projected_unit_cut_rank", "min_input_factor_width"):
        assert empty[key] == hard[key]
