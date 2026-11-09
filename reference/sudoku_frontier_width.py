"""Structural width certificate for generalized-Sudoku exact-cover frontiers.

This measures *potentially live unit-digit obligation bits*, not the
number of reachable states or the rank of a compressed representation.
It does not enumerate assignments, Sudoku completions or factors.

For box order b>=2, side n=b**2 and N=n**2 cells:
  - Every cell ordering has a cut with at least N structural live bits.
  - The row-major ordering attains a maximum of exactly
        W = n**2 + b*n + n = N + N**(3/4) + sqrt(N).
This is a theorem about structural frontiers on full-domain Sudoku,
not an Omega(2**N) runtime or state-count lower bound.

See docs/sudoku-frontier-width.md for the elementary halfway-cut proof.
"""
from __future__ import annotations

from dataclasses import dataclass
from collections.abc import Sequence


@dataclass(frozen=True, slots=True)
class FrontierWidthAudit:
    box: int
    side: int
    cells: int
    max_crossing_units: int
    max_live_obligation_bits: int
    peak_after_cells: int
    half_cut_row_column_units: int
    half_cut_obligation_bits: int


def _validate_box(box: int) -> int:
    if type(box) is not int or box < 1:
        raise ValueError("Sudoku box order must be a positive integer")
    return box * box


def audit_cell_order(box: int, order: Sequence[int]) -> FrontierWidthAudit:
    """Audit the exact *full-domain* row/column/box incidence frontier.

    After processing k cells, an obligation (unit,digit) is potentially
    live exactly when its unit has at least one cell among the first k
    and at least one cell among the remaining N-k.  Since every digit
    is permitted in every blank cell, each crossing unit contributes
    exactly side distinct potential obligation bits.

    Input order must contain every cell exactly once.  A fixed clue or
    sound domain restriction cannot increase the number of *varying*
    frontier bits, though fixed obligations may remain in a key.
    """
    n = _validate_box(box)
    cells = n * n
    if len(order) != cells:
        raise ValueError("Order must contain exactly one entry per cell")
    seen = bytearray(cells)
    counts = [0] * (3 * n)
    crossing_units = 0
    best = 0
    peak_cut = 0
    half_row_col = 0
    half_bits = 0
    half_cut = cells // 2
    for cut, cell in enumerate(order, start=1):
        if type(cell) is not int or cell < 0 or cell >= cells or seen[cell]:
            raise ValueError("Order must be a permutation of all cell indices")
        seen[cell] = 1
        row, col = divmod(cell, n)
        box_id = row // box * box + col // box
        for unit in (row, n + col, 2 * n + box_id):
            previous = counts[unit]
            if 0 < previous < n:
                crossing_units -= 1
            counts[unit] += 1
            if 0 < counts[unit] < n:
                crossing_units += 1
        if crossing_units > best:
            best, peak_cut = crossing_units, cut
        if cut == half_cut:
            half_row_col = sum(0 < x < n for x in counts[:2 * n])
            half_bits = crossing_units * n
    return FrontierWidthAudit(
        box=box, side=n, cells=cells,
        max_crossing_units=best,
        max_live_obligation_bits=n * best,
        peak_after_cells=peak_cut,
        half_cut_row_column_units=half_row_col,
        half_cut_obligation_bits=half_bits,
    )


def row_major_width_audit(box: int) -> FrontierWidthAudit:
    """Construct row-major order and verify its explicit width formula.

    The formula is proved independently in docs/sudoku-frontier-width.md;
    these finite source checks are not a substitute for that proof.
    """
    n = _validate_box(box)
    audit = audit_cell_order(box, range(n * n))
    expected = 0 if box == 1 else n * n + box * n + n
    if audit.max_live_obligation_bits != expected:
        raise AssertionError("Row-major structural width identity failed")
    if box >= 2 and audit.peak_after_cells != n + 1:
        raise AssertionError("Row-major peak witness differs from constructive proof")
    return audit


def row_major_width_formula(box: int) -> int:
    """Symbolic worst-case state-map exponent, never allocate 2**W."""
    n = _validate_box(box)
    return 0 if box == 1 else n * n + box * n + n
