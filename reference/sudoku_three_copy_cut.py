"""Cut-capacity lower bound for the *existing three-copy* Sudoku reduction.

Scope is deliberately narrow: each cell independently sends its digit to
three disjoint row/column/box interfaces using Boolean wires, and each
unit interface must distinguish every possible digit using only that copy.
This does NOT lower-bound arbitrary network encodings or shared/weighted
non-Boolean tensor networks.
"""
from __future__ import annotations

from dataclasses import dataclass

from reference.bit_work import sudoku_direct_encoding_size


@dataclass(frozen=True, slots=True)
class ThreeCopyCut:
    box_order: int
    side: int
    cells: int
    minimum_boolean_wires_per_copy: int
    minimum_three_copy_wires: int
    actual_direct_wires: int
    saturates_cut: bool


def three_copy_cut(box_order: int) -> ThreeCopyCut:
    """Pigeonhole: n distinguishable digits require ceil(log2(n)) bits/copy."""
    if type(box_order) is not int or box_order < 1:
        raise ValueError('positive integer box order required')
    dims = sudoku_direct_encoding_size(box_order)
    bits = (dims.side - 1).bit_length()
    lower = 3 * dims.cells * bits
    return ThreeCopyCut(
        box_order, dims.side, dims.cells, bits, lower,
        dims.wires, lower == dims.wires,
    )
