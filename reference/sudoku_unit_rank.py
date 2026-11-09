"""Exact valid-digit cut decomposition for the canonical Sudoku unit.

A raw UnitEntryOracle accepts *any distinct binary code* up to 2**width-1.
A canonical adjacent CellEntryOracle constrains each code to [0, side).
Only after imposing this already-present domain restriction does the unit
admit the complement-subset decomposition of rank binomial(side, cut).

This does NOT assert that rank is constant, that the raw tensor has exactly
this rank, or that composing row/column/box constraints preserves it.
"""
from __future__ import annotations

from itertools import combinations, islice
from math import comb
from collections.abc import Iterator


def _validate(side: int, cut: int) -> None:
    if (type(side) is not int or side < 1 or
            type(cut) is not int or cut < 0 or cut > side):
        raise ValueError("Sudoku unit cut must lie between zero and side")


def projected_all_different(side: int, digits: tuple[int, ...]) -> int:
    """All-distinct 0/1 unit tensor restricted to legal Sudoku digits."""
    if type(side) is not int or side < 1 or len(digits) != side:
        raise ValueError("Invalid unit shape")
    return int(
        all(type(x) is int and 0 <= x < side for x in digits)
        and len(set(digits)) == side
    )


def subset_factor_entry(side: int, cut: int, digits: tuple[int, ...]) -> int:
    """Contract the EXACT implicit complement-subset rank decomposition.

    Let S range over all k-subsets of [n]. L_S(prefix) is one exactly
    when the prefix uses each digit in S once. R_S(suffix) is one exactly
    when the suffix uses the complementary n-k digits once. At most one
    S contributes for a fixed input, so we never enumerate subsets to
    evaluate a single tensor entry.
    """
    _validate(side, cut)
    if len(digits) != side:
        raise ValueError("Invalid unit degree")
    if any(type(d) is not int or d < 0 or d >= side for d in digits):
        return 0
    left = digits[:cut]
    right = digits[cut:]
    if len(set(left)) != cut or len(set(right)) != side-cut:
        return 0
    left_mask = sum(1 << value for value in left)
    right_mask = sum(1 << value for value in right)
    return int(left_mask == ((1 << side)-1) ^ right_mask)


def unit_subset_rank(side: int, cut: int) -> int:
    """Proven rank of the valid-digit unit matricization over any field.

    Upper bound: decomposition into C(n,k) rank-one subset terms.
    Lower bound: choose one ordering per k-subset as row and the unique
    complementary ordering as column; that minor is the identity.
    Therefore equality holds, including over GF(2).
    """
    _validate(side, cut)
    return comb(side, cut)


def subset_identity_witness(
    side: int, cut: int, *, limit: int = 12,
) -> Iterator[tuple[tuple[int, ...], tuple[int, ...]]]:
    """Stream the first witness minor's diagonal, without a giant table."""
    _validate(side, cut)
    if type(limit) is not int or limit < 0:
        raise ValueError("Witness limit must be nonnegative")
    universe = set(range(side))
    for chosen in islice(combinations(range(side), cut), limit):
        yield chosen, tuple(sorted(universe.difference(chosen)))
