"""Exact continuation/Hankel-rank certificates on small Sudoku.

For a fixed cell cut, prefix frontier signatures determine all
interactions with legal suffix assignments. Distinct *extendable*
signatures have disjoint nonempty suffix languages. Consequently the
0/1 solution tensor's prefix/suffix flattening has rank exactly the
number of extendable signatures over EVERY field.

The mathematical proof holds for all generalized Sudoku sizes; the
small witness enumerator here deliberately handles 4x4 only. It
constructs one genuine completed-grid witness per signature and checks
the corresponding identity minor, rather than expanding the enormous
full prefix-by-suffix matrix.

Digit-orbit counts illustrate symmetry reduction of aggregate counts;
they do NOT reduce the labelled continuation matrix's rank.
"""
from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from itertools import permutations
from math import factorial

from non_exponential_sudoku.sudoku.three_cnf import Puzzle


@dataclass(frozen=True, slots=True)
class ContinuationCutCertificate:
    cut: int
    solutions: int
    structural_frontier_bits: int
    extendable_signatures: int
    exact_flattening_rank: int
    digit_orbits: int
    orbit_sizes: tuple[int, ...]
    identity_minor_verified: bool


def completed_four_by_four_grids() -> tuple[tuple[int, ...], ...]:
    """Independently enumerate all 288 blank 4x4 Sudoku solutions.

    This enumerator is a bounded research oracle and is not used by
    production counting. A general n-grid enumerator is intentionally
    not provided: the number of grids grows very rapidly.
    """
    n, b = 4, 2
    selected = [0] * (n * n)
    used = [0] * (3 * n)
    solutions: list[tuple[int, ...]] = []

    def visit(cell: int) -> None:
        if cell == n * n:
            solutions.append(tuple(selected))
            if len(solutions) > 288:
                raise AssertionError("Unexpectedly many 4x4 completions")
            return
        row, col = divmod(cell, n)
        units = (row, n + col, 2 * n + (row // b) * b + col // b)
        occupied = used[units[0]] | used[units[1]] | used[units[2]]
        for digit in range(1, n + 1):
            bit = 1 << (digit - 1)
            if occupied & bit:
                continue
            selected[cell] = digit
            for unit in units:
                used[unit] |= bit
            visit(cell + 1)
            for unit in units:
                used[unit] ^= bit
        selected[cell] = 0

    visit(0)
    if len(solutions) != 288:
        raise AssertionError("Four-by-four independent count changed")
    return tuple(solutions)


def _crossing_units(puzzle: Puzzle, order: Sequence[int], cut: int) -> tuple[int, ...]:
    side = puzzle.side
    cells = side * side
    if len(order) != cells or set(order) != set(range(cells)):
        raise ValueError("Cell order must be a permutation of all cells")
    if type(cut) is not int or not 0 <= cut <= cells:
        raise ValueError("Cut outside cell order")
    processed = set(order[:cut])
    return tuple(
        index for index, unit in enumerate(puzzle.units())
        if any(cell in processed for cell in unit)
        and any(cell not in processed for cell in unit)
    )


def prefix_signature(
    puzzle: Puzzle, solution: Sequence[int], order: Sequence[int], cut: int,
) -> int:
    """Return used (unit,digit) obligations with a future occurrence.

    Only complete solutions are admitted here; their prefix legality,
    digit range, and fixed clues have already been independently checked.
    """
    if not puzzle.valid_solution(tuple(solution)):
        raise ValueError("Expected a valid complete Sudoku witness")
    mixed = set(_crossing_units(puzzle, order, cut))
    memberships: list[list[int]] = [[] for _ in solution]
    for unit, cells in enumerate(puzzle.units()):
        if unit in mixed:
            for cell in cells:
                memberships[cell].append(unit)
    bits = 0
    for cell in order[:cut]:
        for unit in memberships[cell]:
            bits |= 1 << (unit * puzzle.side + solution[cell] - 1)
    return bits


def _digit_relabel(signature: int, side: int, permutation: Sequence[int]) -> int:
    """Relabel each digit plane, keeping all unit positions unchanged."""
    result = 0
    for unit in range(3 * side):
        for digit in range(side):
            if signature & (1 << (unit * side + digit)):
                result |= 1 << (unit * side + permutation[digit])
    return result


def blank_four_by_four_cut(cut: int) -> ContinuationCutCertificate:
    """Check an identity minor of the full solution tensor at this cut.

    Each representative is a complete-grid witness. Splicing its prefix
    with another representative's suffix is valid exactly when the
    representatives have the same frontier signature. A checked identity
    minor proves a rank lower bound, and the residual-language theorem
    gives the matching upper bound without enumerating all invalid
    prefixes/suffixes.
    """
    puzzle = Puzzle(2, (0,) * 16)
    order = tuple(range(16))
    mixed = _crossing_units(puzzle, order, cut)
    representatives: dict[int, tuple[int, ...]] = {}
    completions = completed_four_by_four_grids()
    for solution in completions:
        signature = prefix_signature(puzzle, solution, order, cut)
        representatives.setdefault(signature, solution)
    signatures = tuple(sorted(representatives))

    for i, left in enumerate(signatures):
        prefix = representatives[left][:cut]
        for j, right in enumerate(signatures):
            suffix = representatives[right][cut:]
            if puzzle.valid_solution(prefix + suffix) != (i == j):
                raise AssertionError("Continuation identity minor failed")

    all_perms = tuple(permutations(range(puzzle.side)))
    unvisited = set(signatures)
    sizes: list[int] = []
    while unvisited:
        original = min(unvisited)
        orbit = {_digit_relabel(original, puzzle.side, perm)
                 for perm in all_perms}
        if not orbit.issubset(representatives):
            raise AssertionError("Digit symmetry did not preserve completeable states")
        unvisited.difference_update(orbit)
        sizes.append(len(orbit))
    return ContinuationCutCertificate(
        cut=cut, solutions=len(completions),
        structural_frontier_bits=len(mixed) * puzzle.side,
        extendable_signatures=len(signatures),
        exact_flattening_rank=len(signatures),
        digit_orbits=len(sizes),
        orbit_sizes=tuple(sorted(sizes)),
        identity_minor_verified=True,
    )


def exact_first_row_rank(box: int) -> int:
    """Proved rank after the first row of an empty generalized Sudoku.

    There are exactly n! legal first-row assignments, and each extends
    by globally permuting digits in a canonical complete Sudoku.
    Different permutations have disjoint suffix languages, hence rank
    is n! over any field.
    """
    if type(box) is not int or box < 1:
        raise ValueError("Box order must be a positive integer")
    return factorial(box * box)
