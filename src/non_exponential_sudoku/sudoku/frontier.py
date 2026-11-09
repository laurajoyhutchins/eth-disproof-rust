"""Exact Sudoku contraction by a bounded frontier of unit-digit obligations.

This is a Sudoku-specialized tensor contraction, not a general polynomial-time
algorithm.  Each cell contributes one of its available digits.  A contribution
uses exactly three constraint bits: (row, digit), (column, digit), (box, digit).
Multiplication rejects repeated constraint bits; addition merges identical
frontier signatures with arbitrary-precision integer coefficients.

A constraint bit is forgotten after the last cell that could use it.  It can
never conflict with another choice after that point, and all constraints are
satisfied at completion because every cell is filled and every Sudoku unit has
exactly ``side`` cells.  Thus forgetting preserves exact solution counts.

No DFS/backtracking, SAT solver, witness, or exhaustive-search fallback is
called.  Complexity is exponential in the maximum *reachable frontier* size;
resource limits are enforced before inserting additional signatures.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Sequence

from .three_cnf import Puzzle
from .state import initial_domains, support_projected_domains


class FrontierCapacityError(RuntimeError):
    """A declared frontier computation limit was reached; no fallback ran."""


@dataclass(frozen=True)
class FrontierLimits:
    max_states: int = 100_000
    max_transitions: int = 5_000_000
    max_estimated_bytes: int = 128 * 1024 * 1024

    def __post_init__(self) -> None:
        if min(self.max_states, self.max_transitions, self.max_estimated_bytes) < 1:
            raise ValueError('Frontier limits must be positive')


@dataclass(frozen=True)
class FrontierStats:
    fixed_cells: int
    free_cells: int
    candidate_choices: int
    max_frontier_bits: int
    peak_states: int
    peak_live_states: int
    transitions: int
    compatible_transitions: int
    merged_transitions: int
    states_processed: int


@dataclass(frozen=True)
class FrontierResult:
    count: int
    stats: FrontierStats




def _empty_stats() -> FrontierStats:
    return FrontierStats(0, 0, 0, 0, 0, 0, 0, 0, 0, 0)


def count_frontier(
    puzzle: Puzzle,
    *,
    limits: FrontierLimits = FrontierLimits(),
    order: Literal['row-major', 'minimum-domain'] = 'row-major',
    domains: Sequence[int] | None = None,
    projection: Literal['singletons', 'matching'] = 'singletons',
) -> FrontierResult:
    """Count Sudoku completions by exact, signature-sharing frontier contraction.

    If ``domains`` is provided, count completions respecting those additional
    candidate restrictions.  Only a *support-preserving* reduction, such as a
    verified all-different projection, can be used to count the original
    puzzle with unrestricted semantics.  Without it, deterministic singleton
    propagation derives all domains solely from the puzzle's givens.
    """
    if order not in ('row-major', 'minimum-domain'):
        raise ValueError('Unknown frontier ordering')
    if projection not in ('singletons', 'matching'):
        raise ValueError('Unknown Sudoku support projection')
    if domains is not None and projection != 'singletons':
        raise ValueError('Matching projection requires puzzle-derived domains')
    n = puzzle.side
    if puzzle.b < 1 or len(puzzle.entries) != n * n or any(
        v < 0 or v > n for v in puzzle.entries
    ):
        raise ValueError('Invalid Sudoku board dimensions or entries')
    units = puzzle.units()
    cell_units: list[list[int]] = [[] for _ in puzzle.entries]
    for u, cells in enumerate(units):
        for cell in cells:
            cell_units[cell].append(u)
    if any(len(used) != 3 for used in cell_units):
        raise ValueError('Expected each Sudoku cell in exactly three units')

    if domains is None:
        initial = (support_projected_domains(puzzle) if projection == 'matching'
                   else initial_domains(puzzle))
        if initial is None:
            return FrontierResult(0, _empty_stats())
    else:
        if len(domains) != n * n:
            raise ValueError('Domain vector length differs from the board')
        full = (1 << n) - 1
        initial = tuple(domains)
        for cell, (mask, given) in enumerate(zip(initial, puzzle.entries)):
            if type(mask) is not int or not 0 < mask <= full or mask & ~full:
                raise ValueError(f'Invalid candidate domain for cell {cell}')
            if given and mask != 1 << (given - 1):
                raise ValueError(f'Domain contradicts given at cell {cell}')

    base = 0
    free: list[int] = []
    options: dict[int, tuple[int, ...]] = {}
    for cell, mask in enumerate(initial):
        choices: list[int] = []
        while mask:
            bit = mask & -mask
            mask ^= bit
            digit = bit.bit_length() - 1
            signature = 0
            for unit in cell_units[cell]:
                signature |= 1 << (unit * n + digit)
            choices.append(signature)
        if len(choices) == 1:
            if base & choices[0]:
                return FrontierResult(0, _empty_stats())
            base |= choices[0]
        else:
            free.append(cell)
            options[cell] = tuple(choices)

    if order == 'minimum-domain':
        free.sort(key=lambda cell: (len(options[cell]), cell))
    # Build the exact set of unit/digit bits that a *future* cell could use.
    # A bit outside this set is dead: no later multiplication can inspect it.
    future = [0] * (len(free) + 1)
    for pos in range(len(free) - 1, -1, -1):
        cell_mask = 0
        for candidate in options[free[pos]]:
            cell_mask |= candidate
        future[pos] = future[pos + 1] | cell_mask

    # Structural frontier width: bits that may have been used by the prefix
    # and may also be inspected by the suffix.  The stored signatures may be
    # substantially sparser than this upper bound.
    possible_prefix = base
    max_frontier_bits = (possible_prefix & future[0]).bit_count()
    for pos, cell in enumerate(free):
        for candidate in options[cell]:
            possible_prefix |= candidate
        max_frontier_bits = max(
            max_frontier_bits, (possible_prefix & future[pos + 1]).bit_count()
        )

    # Conservative allowance for two simultaneously allocated Python dicts
    # and their arbitrary-precision signature/count integers.  It is an
    # estimate, not a measured resident-set-size guarantee.
    bytes_per_state = 160 + 2 * ((3 * n * n + 7) // 8)
    def guard(current: int, next_size: int) -> None:
        if next_size > limits.max_states:
            raise FrontierCapacityError(
                f'Frontier state limit: {next_size} > {limits.max_states}')
        if (current + next_size) * bytes_per_state > limits.max_estimated_bytes:
            raise FrontierCapacityError('Frontier estimated-byte limit')

    table: dict[int, int] = {base & future[0]: 1}
    guard(0, len(table))
    peak_states = len(table)
    peak_live = len(table)
    transitions = 0
    compatible = 0
    merged = 0
    processed = 0
    for pos, cell in enumerate(free):
        next_table: dict[int, int] = {}
        keep = future[pos + 1]
        for signature, multiplicity in table.items():
            processed += 1
            for candidate in options[cell]:
                transitions += 1
                if transitions > limits.max_transitions:
                    raise FrontierCapacityError('Frontier transition limit')
                if signature & candidate:
                    continue
                compatible += 1
                key = (signature | candidate) & keep
                if key in next_table:
                    next_table[key] += multiplicity
                    merged += 1
                else:
                    guard(len(table), len(next_table) + 1)
                    next_table[key] = multiplicity
        peak_live = max(peak_live, len(table) + len(next_table))
        table = next_table
        peak_states = max(peak_states, len(table))
        if not table:
            break
    stats = FrontierStats(
        fixed_cells=n * n - len(free), free_cells=len(free),
        candidate_choices=sum(len(options[c]) for c in free),
        max_frontier_bits=max_frontier_bits,
        peak_states=peak_states, peak_live_states=peak_live,
        transitions=transitions, compatible_transitions=compatible,
        merged_transitions=merged, states_processed=processed,
    )
    return FrontierResult(sum(table.values()), stats)
