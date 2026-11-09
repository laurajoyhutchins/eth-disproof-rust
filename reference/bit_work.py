"""Auditable, deliberately partial bit-work envelopes for the exact solver.

This module does not certify a subexponential algorithm. Its two closed-form
bounds cover only the directly implemented Boolean leaf loop and the Newton
interpolation loop. See docs/bit-complexity.md for the hypotheses and proof.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class DirectLeafWork:
    """Upper bounds on outer-loop operations of ``Network.direct``.

    For a zero-free execution with V vertex oracles all counts except
    assignment_bit_reads are attained. Oracle implementations themselves are
    opaque and are not charged by these counters.
    """

    edge_assignments: int
    vertex_oracle_calls: int
    coefficient_multiplications: int
    coefficient_additions: int
    assignment_bit_reads: int


def direct_leaf_work(edges: int, vertices: int) -> DirectLeafWork:
    """Exact worst-case event counts for a full binary direct contraction.

    The bipartite incidence contract has total port count ``2 * edges``.
    This is a bound on loop events, NOT Python bit operations or oracle cost.
    """
    if edges < 0 or vertices < 0:
        raise ValueError("edges and vertices must be nonnegative")
    assignments = 1 << edges
    return DirectLeafWork(
        edge_assignments=assignments,
        vertex_oracle_calls=assignments * vertices,
        coefficient_multiplications=assignments * vertices,
        coefficient_additions=assignments,
        assignment_bit_reads=assignments * (2 * edges),
    )


@dataclass(frozen=True)
class InterpolationWork:
    """Safe outer-operation bounds for ``core.algebra.interpolate``.

    Each inversion is a whole Padic.inv call, and incurs additional inner
    arithmetic not included in the multiplication/addition counts here.
    """

    points: int
    coefficient_multiplications: int
    coefficient_additions_or_subtractions: int
    coefficient_inversions: int


def interpolation_work(points: int) -> InterpolationWork:
    """Quadratic Newton-interpolation ring-operation envelope.

    At iteration k (0-based), polynomial and basis lengths are <= k+1.
    Two Horner evaluations, one basis scaling and one multiplication by a
    linear factor yield <= 5(k+1)+1 coefficient multiplications. There are
    at most 5(k+1)+1 additions/subtractions and one inversion.
    """
    if points < 0:
        raise ValueError("points must be nonnegative")
    triangular = points * (points + 1) // 2
    return InterpolationWork(
        points=points,
        coefficient_multiplications=5 * triangular + points,
        coefficient_additions_or_subtractions=5 * triangular + points,
        coefficient_inversions=points,
    )


@dataclass(frozen=True)
class SudokuDirectEncodingSize:
    """Exact dimensions of DirectNetwork.from_puzzle, independent of clues."""

    box_order: int
    side: int
    cells: int
    bits_per_digit: int
    wires: int
    vertices: int
    maximum_degree: int
    sufficient_count_precision: int


def sudoku_direct_encoding_size(box_order: int) -> SudokuDirectEncodingSize:
    """Closed-form dimensions of the direct Boolean Sudoku network.

    A box order b has side n=b**2 and N=n**2 cells. There are three
    copies of every cell's t-bit digit, n**2 cell vertices and 3*n unit
    vertices. This is NOT the separate degree-three 3-CNF reduction.
    """
    if box_order < 1:
        raise ValueError("box_order must be positive")
    side = box_order * box_order
    cells = side * side
    bits = max(1, (side - 1).bit_length())
    return SudokuDirectEncodingSize(
        box_order=box_order,
        side=side,
        cells=cells,
        bits_per_digit=bits,
        wires=3 * cells * bits,
        vertices=cells + 3 * side,
        maximum_degree=max(side, 3) * bits,
        sufficient_count_precision=cells * bits + 1,
    )
