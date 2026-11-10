"""Selector/projector equivalence on the *actual* spectral auxiliary.

An exceptional tensor eigenvector u has squared norm 2**t, where t is
the number of off-diagonal local symmetric or antisymmetric components.
The eigenvectors are mutually orthogonal. Hence the exact exceptional
orthogonal projector is

    P = sum_u (u^T u) / <u,u>.

For an incidence coordinate transfer A and a restricted group E,
the selector measurement matrix is B = U A E, whereas the projected
Gram matrix is G = E^T A^T P A E = B^T W B, with W positive diagonal.
Over Q, ker(G) = ker(B) and rowspace(G) = rowspace(B).

Thus *exact row-space availability* is invariant under basis change.
Measurement row count, primitive coefficient L1, lambda witnesses and
the literal (tau,D) admission certificate are NOT invariant: the
projected version must independently check its actual resource/design
bounds. Nothing about construction totality or #SAT bit complexity
follows from this lemma.

This file provides an independently executable finite source-equivalence
witness, not a method that enumerates selectors in the production path.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from non_exponential_sudoku.eth.construction import (
    AuxiliaryLabel, ImplicitAuxiliaryDesign,
)
from non_exponential_sudoku.eth.design import MeasurementDesign, _row_combination


@dataclass(frozen=True, slots=True)
class BasisEquivalenceWitness:
    groups: int
    compared_centers: int
    selector_row_count: int
    projector_row_count: int
    selector_max_l1: int
    projector_max_l1: int
    exact_rowspace_inclusions_checked: int


def _norm_squared(
    auxiliary: ImplicitAuxiliaryDesign,
    selector: tuple[int, ...],
) -> int:
    """The local tensor basis uses 1 on a diagonal, 1,±1 off diagonal."""
    if len(selector) != auxiliary.Q:
        raise ValueError("selector length must equal Q")
    r = auxiliary.r
    count_off_diagonal = 0
    for j in selector:
        if not 0 <= j < r * r:
            raise ValueError("selector basis index outside local dimension")
        if j >= r:
            count_off_diagonal += 1
    return 1 << count_off_diagonal


def projector_from_selectors(
    auxiliary: ImplicitAuxiliaryDesign,
    left: AuxiliaryLabel,
    right: AuxiliaryLabel,
) -> Fraction:
    """Small independent spectral-sum oracle for one projector entry.

    Only permitted on a constructed selector-mode auxiliary. Expensive
    by design, so it is NEVER invoked by the production projector path.
    """
    if auxiliary.measurement_basis != "selectors":
        raise ValueError("source selector expansion required for this oracle")
    return sum((
        Fraction(
            auxiliary.measurement_at(i, left)
            * auxiliary.measurement_at(i, right),
            _norm_squared(auxiliary, selector),
        )
        for i, selector in enumerate(auxiliary.measurement_selectors)
    ), Fraction(0))


def compare_transferred_rowspaces(
    selector: tuple[tuple[int, MeasurementDesign], ...],
    projected: tuple[tuple[int, MeasurementDesign], ...],
) -> BasisEquivalenceWitness:
    """Require BOTH inclusions with independent exact rational witnesses.

    Zero rows and rank deficient sets are covered; the returned value
    reports distinct operational row counts and L1 bounds, not an
    artificial assertion that those resource certificates are equal.
    """
    if len(selector) != len(projected):
        raise AssertionError("number of interpolation centers changed")
    num_groups = 0
    inclusions = 0
    selector_total = projector_total = 0
    selector_l1 = projector_l1 = 0
    for (center, s_design), (other_center, p_design) in zip(selector, projected):
        if center != other_center:
            raise AssertionError("interpolation center changed")
        if (s_design.groups != p_design.groups
                or s_design.clause_groups != p_design.clause_groups):
            raise AssertionError("group ownership changed")
        num_groups += len(s_design.groups)
        for group, s_rows, p_rows in zip(
            s_design.groups, s_design.matrices, p_design.matrices
        ):
            if any(len(row) != len(group) for row in (*s_rows, *p_rows)):
                raise AssertionError("malformed measurement row")
            selector_total += len(s_rows)
            projector_total += len(p_rows)
            selector_l1 = max(selector_l1, *(
                sum(abs(x) for x in row) for row in s_rows
            ), 0)
            projector_l1 = max(projector_l1, *(
                sum(abs(x) for x in row) for row in p_rows
            ), 0)
            for left, right in ((s_rows, p_rows), (p_rows, s_rows)):
                for target in left:
                    _row_combination(
                        right, tuple(Fraction(value) for value in target))
                    inclusions += 1
    return BasisEquivalenceWitness(
        groups=num_groups, compared_centers=len(selector),
        selector_row_count=selector_total,
        projector_row_count=projector_total,
        selector_max_l1=selector_l1,
        projector_max_l1=projector_l1,
        exact_rowspace_inclusions_checked=inclusions,
    )
