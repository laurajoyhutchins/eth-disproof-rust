"""Canonical candidate-domain propagation and exact-cover obligations.

These primitives are independent of any particular counting algorithm.
A candidate occupies one row-digit, one column-digit, and one box-digit
obligation.  Only singleton propagation is automatic; arbitrary supplied
domains restrict the counting problem and are not assumed count-preserving.
"""
from __future__ import annotations

from typing import Sequence
from .three_cnf import Puzzle

def initial_domains(puzzle: Puzzle) -> tuple[int, ...] | None:
    """Deterministic singleton propagation, never removing a valid completion."""
    n = puzzle.side
    entire = (1 << n) - 1
    domains = [1 << (v - 1) if v else entire for v in puzzle.entries]
    while True:
        changed = False
        for unit in puzzle.units():
            singles = 0
            for cell in unit:
                mask = domains[cell]
                if mask == 0:
                    return None
                if mask.bit_count() == 1:
                    if singles & mask:
                        return None
                    singles |= mask
            for cell in unit:
                mask = domains[cell]
                if mask.bit_count() == 1:
                    continue
                reduced = mask & ~singles
                if reduced == 0:
                    return None
                if reduced != mask:
                    domains[cell] = reduced
                    changed = True
        if not changed:
            return tuple(domains)


def candidate_bits(cell: int, digit: int, side: int, block: int) -> int:
    r, c = divmod(cell, side)
    box = (r // block) * block + c // block
    return ((1 << (r * side + digit))
            | (1 << ((side + c) * side + digit))
            | (1 << ((2 * side + box) * side + digit)))


def prepare_residual(
    puzzle: Puzzle, domains: Sequence[int] | None,
) -> tuple[dict[int, tuple[int, ...]], bool]:
    n = puzzle.side
    if puzzle.b < 1 or len(puzzle.entries) != n * n or any(
        value < 0 or value > n for value in puzzle.entries
    ):
        raise ValueError('Invalid Sudoku puzzle')
    if domains is None:
        initial = initial_domains(puzzle)
        if initial is None:
            return {}, False
    else:
        if len(domains) != n * n:
            raise ValueError('Incorrect domain vector length')
        full = (1 << n) - 1
        initial = tuple(domains)
        for cell, (mask, given) in enumerate(zip(initial, puzzle.entries)):
            if type(mask) is not int or not 0 < mask <= full:
                raise ValueError(f'Invalid domain at cell {cell}')
            if given and mask != 1 << (given - 1):
                raise ValueError(f'Domain contradicts given at cell {cell}')

    base = 0
    free: dict[int, tuple[int, ...]] = {}
    for cell, mask in enumerate(initial):
        choices = tuple(
            candidate_bits(cell, digit, n, puzzle.b)
            for digit in range(n) if mask & (1 << digit)
        )
        if len(choices) == 1:
            if base & choices[0]:
                return {}, False
            base |= choices[0]
        else:
            free[cell] = choices
    # A supplied domain may contain choices that collide with a fixed cell.
    # Filter those here, so neither counter can forget a fixed obligation.
    allowed: dict[int, tuple[int, ...]] = {}
    for cell, choices in free.items():
        usable = tuple(candidate for candidate in choices if not candidate & base)
        if not usable:
            return {}, False
        allowed[cell] = usable
    return allowed, True

