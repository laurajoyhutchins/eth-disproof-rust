"""Implicit spectral auxiliary representation against the independent dense oracle."""
from __future__ import annotations

from fractions import Fraction

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, ConstructionLimits, construct_auxiliary, construct_bounded_designs,
    construct_from_schedules, count_bruteforce, count_from_constructed,
    deterministic_schedules,
)
from non_exponential_sudoku.eth.construction import (
    ImplicitAuxiliaryDesign, construct_implicit_auxiliary,
)
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize("r,Q,R", [
    (2, 1, 1), (2, 2, 1), (2, 2, 2),
    (2, 2, 3), (2, 3, 2), (3, 1, 1), (3, 1, 2),
])
def test_implicit_rows_and_measurements_equal_dense_oracle(
    r: int, Q: int, R: int,
) -> None:
    limits = ConstructionLimits(max_dimension=256, max_auxiliary_cells=65_536,
                                max_measurement_rows=512)
    dense = construct_auxiliary(r=r, Q=Q, R=R, limits=limits)
    implicit = construct_implicit_auxiliary(r=r, Q=Q, R=R, limits=limits)
    assert isinstance(implicit, ImplicitAuxiliaryDesign)
    assert implicit.dimension == dense.dimension
    assert implicit.interval == dense.interval
    assert implicit.max_polynomial_degree <= R - 1
    assert len(implicit.measurement_selectors) == len(dense.measurements)
    for u, label in enumerate(dense.labels):
        assert implicit.label_index(label) == u
        for w, target in enumerate(dense.labels):
            assert implicit.row_at(label, target) == dense.rows[u][w]
        for j, measurement in enumerate(dense.measurements):
            assert tuple(implicit.measurement_at(j, target) for target in dense.labels) == measurement


def test_implicit_transfer_matches_dense_exact_count() -> None:
    formula = CNFFormula(3, ((1, -2), (-1, 3), (2, 3)))
    a, d = deterministic_schedules(formula, r=2, Q=2)
    dense = construct_auxiliary(r=2, Q=2, R=2)
    implicit = construct_implicit_auxiliary(r=2, Q=2, R=2)
    full = construct_from_schedules(formula, dense, a, d)
    sparse = construct_from_schedules(formula, implicit, a, d)
    assert full.replacements == sparse.replacements
    assert full.centers == sparse.centers
    assert count_from_constructed(formula, sparse) == count_from_constructed(
        formula, full, readout='polynomial',
    ) == count_bruteforce(formula)


def test_default_constructor_no_longer_needs_dense_rows() -> None:
    formula = CNFFormula(3, ((1, -2), (-1, 3)))
    implicit = construct_bounded_designs(formula, r=2, Q=2, R=2)
    dense = construct_bounded_designs(formula, r=2, Q=2, R=2,
                                      representation='dense')
    assert isinstance(implicit.auxiliary, ImplicitAuxiliaryDesign)
    assert implicit.replacements == dense.replacements
    assert implicit.centers == dense.centers


def test_large_virtual_dimension_and_exceptional_direction_are_lazy() -> None:
    # r=2, R=Q: a single exceptional tensor direction, but D is enormous.
    aux = construct_implicit_auxiliary(r=2, Q=12, R=12)
    assert aux.dimension == 4 ** 12
    assert len(aux.measurement_selectors) == 1
    a = tuple((0, 1) for _ in range(12))
    b = tuple((1, 0) for _ in range(12))
    assert aux.row_at(a, a).at_zero == 1
    assert aux.row_at(a, b).at_zero == 0
    assert aux.row_at(a, b).degree <= 11
    assert aux.measurement_at(0, a) in (-1, 1)
    assert aux.measurement_at(0, b) in (-1, 1)
    # Not even the auxiliary labels are allocated for all D coordinates.
    assert not hasattr(aux, 'labels')
    assert not hasattr(aux, 'rows')


def test_large_dimension_refuses_dense_but_transfers_implicitly() -> None:
    formula = CNFFormula(3, ((1, 2), (-1, 3)))
    with pytest.raises(CapacityError, match='dimension'):
        construct_auxiliary(r=2, Q=5, R=5)
    a, d = deterministic_schedules(formula, r=2, Q=5)
    aux = construct_implicit_auxiliary(r=2, Q=5, R=5)
    transferred = construct_from_schedules(formula, aux, a, d)
    assert len(transferred.centers) == 5
    assert transferred.replacements.validate(formula) is None
    assert transferred.max_measurement_rows <= 10


def test_implicit_rejects_excessive_measurements_before_enumeration() -> None:
    with pytest.raises(CapacityError, match='exceptional direction'):
        construct_implicit_auxiliary(r=2, Q=12, R=2)
    with pytest.raises(CapacityError, match='point'):
        construct_implicit_auxiliary(r=2, Q=12, R=12,
                                     limits=ConstructionLimits(max_implicit_points=8))
