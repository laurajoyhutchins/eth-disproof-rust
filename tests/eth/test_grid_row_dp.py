"""An independent row-transfer counter for the planar grid-port fixture.

The grid-port family has n=4k**2 variables and just 4k vertices in any
horizontal row. An exact DP can retain boundary information rather than
enumerate 2**n assignments. This tests a *conventional* 2**O(sqrt(n))
method; it is not an ETH lower bound or a speed claim for spectral code.
"""
from __future__ import annotations

import pytest

from non_exponential_sudoku.eth import CNFFormula, count_bruteforce
from reference.eth_bounded_incidence_fixtures import (
    alternating_signs, subcubic_grid_cnf,
)


def _count_grid_rows(formula: CNFFormula, side: int) -> int:
    """Exact signed 2-CNF row DP with O(side*2**(4*side)) row scan.

    A boundary clause (a OR b) fails only when both its literals are
    false. Aggregate the previous row's assignments by the subset of
    boundary literals that are false, then use a subset-zeta transform
    to sum compatible signatures. No 2**n Boolean truth table is made.
    """
    width = 4 * side
    if formula.nvars != side * width:
        raise ValueError("grid row dimension mismatch")
    expected = {
        frozenset(abs(v) for v in clause)
        for clause in subcubic_grid_cnf(side).clauses
    }
    actual = {
        frozenset(abs(v) for v in clause)
        for clause in formula.clauses
    }
    if expected != actual or len(formula.clauses) != len(expected):
        raise ValueError("not the expected unsigned grid-port incidence")

    # Entry: (local index, positive literal, local index, positive literal).
    inside: list[list[tuple[int, bool, int, bool]]] = [
        [] for _ in range(side)
    ]
    across: list[list[tuple[int, bool, int, bool]]] = [
        [] for _ in range(side - 1)
    ]
    for clause in formula.clauses:
        if len(clause) != 2:
            raise ValueError("grid-port clauses must have width two")
        left, right = clause
        above = (abs(left) - 1) // width
        below = (abs(right) - 1) // width
        if above == below:
            inside[above].append((
                (abs(left) - 1) % width, left > 0,
                (abs(right) - 1) % width, right > 0,
            ))
            continue
        if above > below:
            above, below = below, above
            left, right = right, left
        if below != above + 1:
            raise ValueError("nonadjacent grid rows")
        across[above].append((
            (abs(left) - 1) % width, left > 0,
            (abs(right) - 1) % width, right > 0,
        ))
    if any(len(boundary) != side for boundary in across):
        raise ValueError("grid boundary width mismatch")

    signatures = 1 << side
    previous = [0] * signatures
    compatible = [0] * signatures
    for row in range(side):
        if row:
            # Sum[mask] = number of assignments with bad boundary subset
            # contained in mask (subset zeta transform).
            compatible = previous.copy()
            for bit in range(side):
                for mask in range(signatures):
                    if mask & (1 << bit):
                        compatible[mask] += compatible[mask ^ (1 << bit)]
        current = [0] * signatures
        for assignment in range(1 << width):
            if any(
                (bool(assignment & (1 << a)) != sign_a
                 and bool(assignment & (1 << b)) != sign_b)
                for a, sign_a, b, sign_b in inside[row]
            ):
                continue

            if row:
                top_bad = sum(
                    1 << index
                    for index, (_, _, b, positive) in enumerate(across[row - 1])
                    if bool(assignment & (1 << b)) != positive
                )
                ways = compatible[(signatures - 1) ^ top_bad]
            else:
                ways = 1
            if ways == 0:
                continue
            if row + 1 < side:
                bottom_bad = sum(
                    1 << index
                    for index, (a, positive, _, _) in enumerate(across[row])
                    if bool(assignment & (1 << a)) != positive
                )
            else:
                bottom_bad = 0
            current[bottom_bad] += ways
        previous = current
    return sum(previous)


@pytest.mark.integration
@pytest.mark.parametrize(("signed", "expected"), (
    (False, 1649), (True, 147),
))
def test_two_by_two_row_dp_matches_exhaustive_oracle(
    signed: bool, expected: int,
) -> None:
    unsigned = subcubic_grid_cnf(2)
    formula = alternating_signs(unsigned) if signed else unsigned
    assert _count_grid_rows(formula, 2) == count_bruteforce(formula) == expected


@pytest.mark.integration
@pytest.mark.parametrize(("signed", "expected"), (
    (False, 3447177485121), (True, 17776),
))
def test_four_by_four_grid_can_be_counted_without_two_to_n_enumeration(
    signed: bool, expected: int,
) -> None:
    # 64 Boolean variables: 2**64 exhaustive assignment enumeration
    # is not run. This is a fixed regression of the independent row
    # DP, NOT comparison to a full-cube oracle at this size.
    unsigned = subcubic_grid_cnf(4)
    formula = alternating_signs(unsigned) if signed else unsigned
    assert _count_grid_rows(formula, 4) == expected


@pytest.mark.checkpoint
def test_grid_row_counter_rejects_broken_structure() -> None:
    original = subcubic_grid_cnf(2)
    broken = CNFFormula(original.nvars, original.clauses[:-1])
    with pytest.raises(ValueError, match="incidence"):
        _count_grid_rows(broken, 2)
