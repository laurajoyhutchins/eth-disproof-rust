"""Canonical candidate-domain propagation and exact-cover obligations.

These primitives are independent of any particular counting algorithm.
A candidate occupies one row-digit, one column-digit, and one box-digit
obligation.  Only singleton propagation is automatic; arbitrary supplied
domains restrict the counting problem and are not assumed count-preserving.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Literal, Sequence
from ..runtime.budget import CapacityError
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


@dataclass(frozen=True)
class SupportProjectionLimits:
    """Bound matching work without changing the counting semantics."""

    max_candidates: int = 500_000
    max_matching_checks: int = 2_000_000
    max_unit_scans: int = 200_000

    def __post_init__(self) -> None:
        if (type(self.max_candidates) is not int or self.max_candidates < 1
                or type(self.max_matching_checks) is not int or self.max_matching_checks < 1
                or type(self.max_unit_scans) is not int or self.max_unit_scans < 1):
            raise ValueError('Support projection limits must be positive integers')


def _has_unit_matching(masks: Sequence[int], side: int) -> bool:
    """Polynomial bipartite matching for one all-different Sudoku unit."""
    matched = [-1] * side

    def augment(cell: int, visited: list[bool]) -> bool:
        remaining = masks[cell]
        while remaining:
            bit = remaining & -remaining
            remaining ^= bit
            digit = bit.bit_length() - 1
            if not visited[digit]:
                visited[digit] = True
                if matched[digit] < 0 or augment(matched[digit], visited):
                    matched[digit] = cell
                    return True
        return False

    return all(augment(cell, [False] * side)
               for cell in sorted(range(len(masks)), key=lambda index: masks[index].bit_count()))


def support_projected_domains(
    puzzle: Puzzle, *, limits: SupportProjectionLimits = SupportProjectionLimits(),
) -> tuple[int, ...] | None:
    """Remove only candidates unsupported by a unit's perfect matching.

    This deterministic, nonbranching fixed point preserves every full Sudoku
    completion. All results and limits are independent of any counting backend.
    A contradiction returns None; a work-budget refusal raises CapacityError.
    """
    side = puzzle.side
    if (puzzle.b < 1 or len(puzzle.entries) != side * side or any(
            type(value) is not int or value < 0 or value > side
            for value in puzzle.entries)):
        raise ValueError('Invalid Sudoku board dimensions or entries')
    if side ** 3 > limits.max_candidates:
        raise CapacityError('Sudoku matching-projection candidate limit')
    initial = initial_domains(puzzle)
    if initial is None:
        return None
    domains = list(initial)
    units = tuple(tuple(unit) for unit in puzzle.units())
    incident: list[list[int]] = [[] for _ in domains]
    for index, unit in enumerate(units):
        for cell in unit:
            incident[cell].append(index)

    pending = deque(range(len(units)))
    enqueued = set(range(len(units)))
    previous: list[tuple[int, ...] | None] = [None] * len(units)
    checks = 0
    scans = 0

    def matching(masks: Sequence[int]) -> bool:
        nonlocal checks
        checks += 1
        if checks > limits.max_matching_checks:
            raise CapacityError('Sudoku matching-projection work limit')
        return _has_unit_matching(masks, side)

    while pending:
        index = pending.popleft()
        enqueued.remove(index)
        unit = units[index]
        signature = tuple(domains[cell] for cell in unit)
        if previous[index] == signature:
            continue
        previous[index] = signature
        scans += 1
        if scans > limits.max_unit_scans:
            raise CapacityError('Sudoku matching-projection unit-scan limit')
        if not matching(signature):
            return None
        for position, cell in enumerate(unit):
            remaining = domains[cell]
            while remaining:
                bit = remaining & -remaining
                remaining ^= bit
                if not domains[cell] & bit or domains[cell] == bit:
                    continue
                proposed = [domains[member] for member in unit]
                proposed[position] = bit
                if matching(proposed):
                    continue
                domains[cell] &= ~bit
                if domains[cell] == 0:
                    return None
                for affected in incident[cell]:
                    if affected not in enqueued:
                        pending.append(affected)
                        enqueued.add(affected)
    return tuple(domains)


def candidate_bits(cell: int, digit: int, side: int, block: int) -> int:
    r, c = divmod(cell, side)
    box = (r // block) * block + c // block
    return ((1 << (r * side + digit))
            | (1 << ((side + c) * side + digit))
            | (1 << ((2 * side + box) * side + digit)))


def prepare_residual(
    puzzle: Puzzle, domains: Sequence[int] | None,
    *, projection: Literal['singletons', 'matching'] = 'singletons',
) -> tuple[dict[int, tuple[int, ...]], bool]:
    n = puzzle.side
    if puzzle.b < 1 or len(puzzle.entries) != n * n or any(
        value < 0 or value > n for value in puzzle.entries
    ):
        raise ValueError('Invalid Sudoku puzzle')
    if projection not in ('singletons', 'matching'):
        raise ValueError('Unknown Sudoku support projection')
    if domains is None:
        initial = (support_projected_domains(puzzle) if projection == 'matching'
                   else initial_domains(puzzle))
        if initial is None:
            return {}, False
    else:
        if projection != 'singletons':
            raise ValueError('Matching projection requires puzzle-derived domains')
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

