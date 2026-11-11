"""Retain an exact integer selector subbasis, not a large Gram primitive row.

The spectral projector identifies exactly the selector row space, but
its canonical fraction-free Gram RREF can have much larger integer L1
norms. This routine keeps an independent SUBSET of original selector
rows, so the numerical row norm can never increase.

The input row generator is already a list/iterator of exact integer
selector measurements. The routine does NOT find rows of an implicit
selector operator, prove balancing, or remove the source's selector
enumeration cap. Its constructive worst-case cost is polynomial in
the number/width/bit-length of the supplied rows.

The pivot fractions have determinants of input submatrices as their
numerators and denominators. The bit-length bound is consequently
O(k*(log(max_entry)+log(k+1))), k<=min(width, number_of_rows).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable

from .design import MeasurementDesign


def _bits(x: int) -> int:
    return max(1, abs(x).bit_length())


@dataclass(frozen=True, slots=True)
class SelectorSubbasisStats:
    input_rows: int
    selected_rows: int
    rank: int
    maximum_input_l1: int
    maximum_selected_l1: int
    maximum_fraction_component_bits: int
    fraction_component_bits_upper: int
    pivot_reduction_operations: int


@dataclass(frozen=True, slots=True)
class SelectorSubbasis:
    rows: tuple[tuple[int, ...], ...]
    stats: SelectorSubbasisStats


def independent_selector_rows(
    source_rows: Iterable[tuple[int, ...]],
    *, width: int, max_l1: int | None = None,
) -> SelectorSubbasis:
    """Keep original independent rows, never Gram-derived integer rows.

    Every retained row was present in source_rows, so if the original
    selector transfer obeyed L1<=D, the compressed transfer does too.
    """
    if type(width) is not int or width < 0:
        raise ValueError("selector subbasis width must be nonnegative")
    if max_l1 is not None and (type(max_l1) is not int or max_l1 < 0):
        raise ValueError("selector L1 bound must be nonnegative")

    source_count = 0
    selected: list[tuple[int, ...]] = []
    echelon: list[tuple[int, tuple[Fraction, ...]]] = []
    max_input_l1 = 0
    max_fraction_bits = 1
    reduction_ops = 0

    for row in source_rows:
        if len(row) != width or any(type(x) is not int for x in row):
            raise ValueError("selector row must have exact integer width")
        source_count += 1
        l1 = sum(abs(x) for x in row)
        if max_l1 is not None and l1 > max_l1:
            raise ValueError("selector row exceeds declared L1 bound")
        max_input_l1 = max(max_input_l1, l1)
        residual = [Fraction(x) for x in row]
        for pivot, normalized in echelon:
            factor = residual[pivot]
            if factor:
                residual = [a - factor * b
                            for a, b in zip(residual, normalized)]
                reduction_ops += width
        for value in residual:
            max_fraction_bits = max(
                max_fraction_bits,
                _bits(value.numerator), _bits(value.denominator),
            )
        pivot = next((j for j, value in enumerate(residual) if value), None)
        if pivot is not None:
            leading = residual[pivot]
            normalized = tuple(x / leading for x in residual)
            for value in normalized:
                max_fraction_bits = max(
                    max_fraction_bits,
                    _bits(value.numerator), _bits(value.denominator),
                )
            echelon.append((pivot, normalized))
            selected.append(row)
    rank = len(selected)
    max_entry_bits = _bits(max_input_l1)
    # Rational pivot entries are ratios of determinants of matrices of
    # order <=rank. Bound each determinant by rank! * L1**rank.
    ceiling = rank * (max_entry_bits + (rank + 1).bit_length()) + 5
    if max_fraction_bits > ceiling:
        raise ArithmeticError("selector pivot minors exceeded height bound")
    return SelectorSubbasis(
        tuple(selected),
        SelectorSubbasisStats(
            input_rows=source_count,
            selected_rows=rank,
            rank=rank,
            maximum_input_l1=max_input_l1,
            maximum_selected_l1=max(
                (sum(abs(x) for x in row) for row in selected), default=0),
            maximum_fraction_component_bits=max_fraction_bits,
            fraction_component_bits_upper=ceiling,
            pivot_reduction_operations=reduction_ops,
        ),
    )


def prune_selector_design(
    design: MeasurementDesign,
) -> tuple[MeasurementDesign, tuple[SelectorSubbasisStats, ...]]:
    """Equivalent exact rowspace with tau, D recalculated conservatively.

    Keeps clause ownership/group order. It does not re-certify a CNF's
    occurrence witnesses; callers must invoke certify_measurements.
    """
    if len(design.groups) != len(design.matrices):
        raise ValueError("selector group and measurement counts differ")
    subsets = tuple(
        independent_selector_rows(rows, width=len(group), max_l1=design.D)
        for group, rows in zip(design.groups, design.matrices)
    )
    new_matrices = tuple(subset.rows for subset in subsets)
    count = sum(map(len, new_matrices))
    n = sum(map(len, design.groups))
    d = max((
        sum(abs(x) for x in row)
        for rows in new_matrices for row in rows
    ), default=0)
    return MeasurementDesign(
        groups=design.groups,
        clause_groups=design.clause_groups,
        matrices=new_matrices,
        tau=Fraction(count, 2 * n) if n else Fraction(0),
        D=d,
    ), tuple(subset.stats for subset in subsets)
