"""Exact projector compression of the full exceptional measurement row space."""
from __future__ import annotations

from fractions import Fraction

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, ConstructionLimits, construct_auxiliary,
    construct_bounded_designs, construct_from_schedules,
    count_bruteforce, count_from_constructed, deterministic_schedules,
)
from non_exponential_sudoku.eth.construction import construct_implicit_auxiliary
from non_exponential_sudoku.eth.design import _row_combination
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize("r,Q,R", [
    (2, 1, 1), (2, 2, 1), (2, 2, 2), (2, 2, 3),
    (2, 3, 2), (3, 1, 1), (3, 1, 2),
])
def test_projector_matches_independent_orthogonal_eigenvector_sum(
    r: int, Q: int, R: int,
) -> None:
    limits = ConstructionLimits(max_dimension=256, max_auxiliary_cells=65_536,
                                max_measurement_rows=512)
    dense = construct_auxiliary(r=r, Q=Q, R=R, limits=limits)
    projected = construct_implicit_auxiliary(
        r=r, Q=Q, R=R, limits=limits, measurement_basis='projector')
    assert projected.exceptional_count == len(dense.measurements)
    assert projected.measurement_selectors == ()
    with pytest.raises(ValueError, match='no enumerated selectors'):
        projected.measurement_at(0, dense.labels[0])
    # The original tensor rows are an orthogonal (not normalized) basis.
    lengths = [sum(value * value for value in row) for row in dense.measurements]
    for i, left in enumerate(dense.labels):
        for j, right in enumerate(dense.labels):
            expected = sum(
                (Fraction(row[i] * row[j], norm)
                 for row, norm in zip(dense.measurements, lengths)),
                Fraction(0),
            )
            assert projected.exceptional_projector_at(left, right) == expected


@pytest.mark.parametrize("Q,R", [(2, 1), (2, 2), (3, 2)])
def test_projected_transfer_has_exactly_same_row_space_and_count(
    Q: int, R: int,
) -> None:
    formula = CNFFormula(3, ((1, -2), (-1, 3), (2, 3)))
    a, d = deterministic_schedules(formula, r=2, Q=Q)
    limits = ConstructionLimits(max_dimension=256, max_auxiliary_cells=65_536,
                                max_measurement_rows=512)
    original_aux = construct_auxiliary(r=2, Q=Q, R=R, limits=limits)
    projected_aux = construct_implicit_auxiliary(
        r=2, Q=Q, R=R, limits=limits, measurement_basis='projector')
    original = construct_from_schedules(formula, original_aux, a, d, limits=limits)
    compressed = construct_from_schedules(formula, projected_aux, a, d, limits=limits)
    assert original.replacements == compressed.replacements
    for (_, a_design), (_, b_design) in zip(original.centers, compressed.centers):
        assert a_design.groups == b_design.groups
        for group, a_rows, b_rows in zip(a_design.groups, a_design.matrices, b_design.matrices):
            assert all(len(row) == len(group) for row in b_rows)
            assert len(b_rows) <= len(a_rows)
            for row in a_rows:
                coefficients = _row_combination(b_rows, tuple(map(Fraction, row)))
                assert len(coefficients) == len(b_rows)
            for row in b_rows:
                _row_combination(a_rows, tuple(map(Fraction, row)))
    assert count_from_constructed(formula, compressed) == count_from_constructed(
        formula, original, readout='polynomial') == count_bruteforce(formula)


def test_implicit_projector_enables_large_exceptional_space_count() -> None:
    # Previously Q=12, R=2 refused even construction because the global
    # exceptional eigenspace has astronomically many explicit basis vectors.
    formula = CNFFormula(3, ((1, 2), (-1, 3)))
    auxiliary = construct_implicit_auxiliary(
        r=2, Q=12, R=2, measurement_basis='projector')
    assert auxiliary.exceptional_count > 128
    assert not auxiliary.measurement_selectors
    a, d = deterministic_schedules(formula, r=2, Q=12)
    constructed = construct_from_schedules(formula, auxiliary, a, d)
    assert constructed.max_measurement_rows <= 128
    assert count_from_constructed(formula, constructed) == count_bruteforce(formula) == 4


def test_projector_limits_apply_to_actual_rows_not_global_basis() -> None:
    formula = CNFFormula(3, ((1, 2), (-1, 3)))
    limits = ConstructionLimits(max_measurement_rows=1)
    auxiliary = construct_implicit_auxiliary(
        r=2, Q=12, R=2, limits=limits, measurement_basis='projector')
    a, d = deterministic_schedules(formula, r=2, Q=12)
    with pytest.raises(CapacityError, match='transferred measurement row'):
        construct_from_schedules(formula, auxiliary, a, d, limits=limits)


def test_optional_projector_selection_is_explicit() -> None:
    formula = CNFFormula(3, ((1, 2), (-1, 3)))
    constructed = construct_bounded_designs(
        formula, r=2, Q=3, R=2, schedule='digits', measurement_basis='projector')
    assert constructed.auxiliary.measurement_basis == 'projector'
    with pytest.raises(ValueError, match='dense auxiliary'):
        construct_bounded_designs(
            formula, r=2, Q=2, R=2, schedule='digits',
            representation='dense', measurement_basis='projector')
