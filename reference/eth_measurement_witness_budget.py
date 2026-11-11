"""Intermediate rational bit-cost bound for the source measurement witness solver.

Source correspondence: eth/design.py::_row_combination.  This bounds every
reduced Fraction in rectangular exact Gauss-Jordan, not only final lambdas.

Integerize the augmented matrix by multiplying by the product H of target
denominators. Each elimination entry is a ratio of subdeterminants of that
integer matrix. Leibniz's determinant expansion bounds their heights.
A deliberately slack factor covers intermediate Fraction products and
the source's explicit reconstruction of every target coordinate.

This bound covers a supplied matrix and target, not selector enumeration,
spectral balancing, construction of transfer polynomials, or Lean runtime.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence


def _bits(value: int | Fraction) -> int:
    f = Fraction(value)
    return max(1, abs(f.numerator).bit_length(), f.denominator.bit_length())


def _ceil_log2(value: int) -> int:
    if value < 1:
        raise ValueError("expected positive integer")
    return (value - 1).bit_length()


@dataclass(frozen=True, slots=True)
class WitnessBitBudget:
    group_width: int
    measurement_rows: int
    input_scalar_count: int
    input_max_bits: int
    integerized_entry_max_bits: int
    determinant_bits_upper: int
    intermediate_fraction_bits_upper: int
    rational_operations_upper: int
    retained_fraction_slots_upper: int


def witness_bit_budget(
    rows: Sequence[Sequence[int]], target: Sequence[int | Fraction],
) -> WitnessBitBudget:
    """Polynomial bit and simultaneous storage bounds for exact row solving.

    The source can reject an inconsistent system. Its attempted elimination
    still obeys these same ceilings. All terms are integer-only bounds.
    """
    g, s = len(target), len(rows)
    if any(len(row) != g for row in rows):
        raise ValueError("measurement matrix width mismatch")
    if any(type(entry) is not int for row in rows for entry in row):
        raise ValueError("measurement coefficients must be exact integers")
    if any(type(value) not in (int, Fraction) for value in target):
        raise ValueError("target entries must be exact rational numbers")
    rhs = tuple(Fraction(value) for value in target)
    common = 1
    for value in rhs:
        common *= value.denominator
    integerized_max = max(
        (abs(entry) * common for row in rows for entry in row), default=0,
    )
    for value in rhs:
        integerized_max = max(
            integerized_max, abs(value.numerator) * (common // value.denominator),
        )
    input_max_bits = max(
        [_bits(value) for row in rows for value in row]
        + [_bits(value) for value in rhs] + [1],
    )
    B = max(1, integerized_max.bit_length())
    rank_ceiling = min(g, s)
    # Every minor has order <=rank+1. The bit bound includes the
    # factorial number of Leibniz terms; 0x0 minors are handled.
    minor_bits = (rank_ceiling + 1) * (
        B + _ceil_log2(rank_ceiling + 2) + 2
    )
    # The normalized Gauss-Jordan entries are minor ratios. Charge
    # source Fraction mul/add/div temporaries and the final <=s-term
    # reconstruction using an intentionally generous polynomial factor.
    height = 16 * (s + 1) * (
        minor_bits + B + _ceil_log2(s + 2) + 8
    )
    # Pivot normalization O(s), elimination O(g*s) for at most
    # min(g,s) pivots, and final O(g*s) exact reconstruction.
    ops = 32 * (g + 1) * (s + 1) * (rank_ceiling + 1)
    # Augmented matrix, normalized row, one replacement row, pivot
    # columns and final solution; no storage for a Boolean cube.
    slots = 4 * (g + 1) * (s + 1) + 4 * (g + s + 2)
    return WitnessBitBudget(
        group_width=g,
        measurement_rows=s,
        input_scalar_count=g * (s + 1),
        input_max_bits=input_max_bits,
        integerized_entry_max_bits=B,
        determinant_bits_upper=minor_bits,
        intermediate_fraction_bits_upper=height,
        rational_operations_upper=ops,
        retained_fraction_slots_upper=slots,
    )


@dataclass(frozen=True, slots=True)
class WitnessTrace:
    coefficients: tuple[Fraction, ...]
    measured_fraction_bits: int
    measured_rational_operations: int


def traced_row_combination(
    rows: tuple[tuple[int, ...], ...], target: tuple[Fraction, ...],
) -> WitnessTrace:
    """Instrument independent source-shaped elimination with exact Fractions.

    The measured operations are field operations, NOT bit-machine steps.
    Production eth.design._row_combination is the differential target.
    """
    width, nrows = len(target), len(rows)
    if any(len(row) != width for row in rows):
        raise ValueError("measurement matrix width mismatch")
    ops, max_bits = 0, 1

    def record(value: Fraction, *, charge: int = 1) -> Fraction:
        nonlocal max_bits, ops
        max_bits = max(max_bits, _bits(value))
        ops += charge
        return value

    augmented = [
        [record(Fraction(rows[j][i]), charge=0) for j in range(nrows)]
        + [record(target[i], charge=0)]
        for i in range(width)
    ]
    pivot_columns: list[int] = []
    pivot_row = 0
    for column in range(nrows):
        pivot = next(
            (i for i in range(pivot_row, width) if augmented[i][column]), None,
        )
        if pivot is None:
            continue
        augmented[pivot_row], augmented[pivot] = augmented[pivot], augmented[pivot_row]
        scale = augmented[pivot_row][column]
        augmented[pivot_row] = [
            record(value / scale) for value in augmented[pivot_row]
        ]
        for row_idx in range(width):
            if row_idx == pivot_row:
                continue
            factor = augmented[row_idx][column]
            if factor:
                augmented[row_idx] = [
                    record(a - record(factor * b))
                    for a, b in zip(augmented[row_idx], augmented[pivot_row])
                ]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == width:
            break
    if any(not any(row[:nrows]) and row[nrows] for row in augmented):
        raise ValueError("cross-group vector outside measurement row space")
    solution = [Fraction(0) for _ in range(nrows)]
    for i, column in enumerate(pivot_columns):
        solution[column] = augmented[i][nrows]
    for i in range(width):
        reconstructed = Fraction(0)
        for j in range(nrows):
            reconstructed = record(
                reconstructed + record(solution[j] * rows[j][i]),
            )
        if reconstructed != target[i]:
            raise ValueError("cross-group vector outside measurement row space")
    return WitnessTrace(tuple(solution), max_bits, ops)
