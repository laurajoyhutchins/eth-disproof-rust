"""Exact digit-symmetry quotients for Sudoku frontier contraction.

A group may permute digits only when it preserves *every cell domain*.
The group acts on each live unit/digit frontier bit by the same permutation.
Its orbit-aggregated multiplicities count all original partial assignments.

This is a finite-size contraction experiment, not an asymptotic improvement.
The full digit-permutation stabilizer is normally much larger than PGL(2,8).
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from math import factorial
from typing import Literal, Sequence

from .frontier import FrontierCapacityError, FrontierLimits
from .state import initial_domains
from .three_cnf import Puzzle

SymmetryMode = Literal['permutations', 'pgl2']
OrbitMode = Literal['permutations', 'pgl2', 'suffix-permutations']


def _gf8_multiply(a: int, b: int) -> int:
    """GF(8) with irreducible modulus X^3 + X + 1."""
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 8:
            a ^= 0b1011
        b >>= 1
    return result


def _gf8_inverse(value: int) -> int:
    if not value:
        raise ZeroDivisionError('zero in GF(8)')
    for candidate in range(1, 8):
        if _gf8_multiply(value, candidate) == 1:
            return candidate
    raise AssertionError('nonzero field element without inverse')


@lru_cache(maxsize=1)
def pgl2_f8_permutations() -> tuple[tuple[int, ...], ...]:
    """Enumerate the faithful, 504-element PGL2(F8) action on P^1(F8).

    Labels 0..7 denote GF(8) elements, and label 8 denotes infinity.
    """
    result: set[tuple[int, ...]] = set()
    for a, b, c, d in product(range(8), repeat=4):
        if _gf8_multiply(a, d) == _gf8_multiply(b, c):
            continue
        images: list[int] = []
        for x in range(9):
            if x == 8:
                num, den = a, c
            else:
                num = _gf8_multiply(a, x) ^ b
                den = _gf8_multiply(c, x) ^ d
            images.append(8 if not den else _gf8_multiply(num, _gf8_inverse(den)))
        result.add(tuple(images))
    if len(result) != 504:
        raise AssertionError('PGL2(F8) action must have order 504')
    return tuple(sorted(result))


def _permute_mask(mask: int, permutation: tuple[int, ...]) -> int:
    result = 0
    while mask:
        bit = mask & -mask
        result |= 1 << permutation[bit.bit_length() - 1]
        mask ^= bit
    return result


@dataclass(frozen=True)
class DigitSymmetry:
    side: int
    mode: SymmetryMode
    classes: tuple[tuple[int, ...], ...]
    permutations: tuple[tuple[int, ...], ...]
    stripe: int

    @property
    def order(self) -> int:
        if self.mode == 'permutations':
            result = 1
            for group in self.classes:
                result *= factorial(len(group))
            return result
        return len(self.permutations)

    def canonical(self, signature: int) -> int:
        """Choose one key per orbit without enumerating the orbit's states."""
        n = self.side
        planes = [(signature >> digit) & self.stripe for digit in range(n)]
        if self.mode == 'permutations':
            for group in self.classes:
                ordered = sorted(planes[digit] for digit in group)
                for digit, plane in zip(group, ordered):
                    planes[digit] = plane
            return sum(plane << digit for digit, plane in enumerate(planes))
        return min(
            sum(planes[digit] << perm[digit] for digit in range(n))
            for perm in self.permutations
        )

    def orbit_size(self, signature: int) -> int:
        """Number of *distinct* raw signatures represented by this key."""
        planes = [(signature >> digit) & self.stripe for digit in range(self.side)]
        if self.mode == 'permutations':
            result = 1
            for group in self.classes:
                counts: dict[int, int] = {}
                for digit in group:
                    plane = planes[digit]
                    counts[plane] = counts.get(plane, 0) + 1
                size = factorial(len(group))
                for multiplicity in counts.values():
                    size //= factorial(multiplicity)
                result *= size
            return result
        stabilizer = sum(
            all(planes[digit] == planes[perm[digit]]
                for digit in range(self.side))
            for perm in self.permutations
        )
        return len(self.permutations) // stabilizer


def _symmetry_for_masks(domains: Sequence[int], side: int,
                        mode: SymmetryMode) -> DigitSymmetry:
    """The group stabilizing an ordered sequence of remaining domains."""
    if side < 1:
        raise ValueError('Sudoku side must be positive')
    full = (1 << side) - 1
    if any(type(mask) is not int or not 0 < mask <= full for mask in domains):
        raise ValueError('Invalid domain for symmetry construction')
    classes_by_signature: dict[int, list[int]] = {}
    for digit in range(side):
        fingerprint = sum(1 << cell for cell, mask in enumerate(domains)
                          if mask & (1 << digit))
        classes_by_signature.setdefault(fingerprint, []).append(digit)
    classes = tuple(tuple(group) for group in classes_by_signature.values())
    if mode == 'permutations':
        perms: tuple[tuple[int, ...], ...] = ()
    elif mode == 'pgl2':
        if side != 9:
            raise ValueError('PGL2(F8) acts on precisely nine labels')
        permitted = set(domains)
        perms = tuple(perm for perm in pgl2_f8_permutations()
                      if all(_permute_mask(mask, perm) == mask
                             for mask in permitted))
    else:
        raise ValueError('Unknown digit symmetry mode')
    stripe = sum(1 << (unit * side) for unit in range(3 * side))
    return DigitSymmetry(side, mode, classes, perms, stripe)


def symmetry_for_domains(domains: Sequence[int], side: int,
                         mode: SymmetryMode = 'permutations') -> DigitSymmetry:
    """Find the digit subgroup preserving every cell's domain."""
    if len(domains) != side * side:
        raise ValueError('Expected one domain per Sudoku cell')
    return _symmetry_for_masks(domains, side, mode)


@dataclass(frozen=True)
class OrbitFrontierStats:
    group_order: int
    free_cells: int
    processed_cells: int
    peak_orbits: int
    final_orbits: int
    final_raw_states: int
    candidate_transitions: int
    compatible_transitions: int
    merged_transitions: int
    final_group_order: int = 0


@dataclass(frozen=True)
class OrbitFrontierResult:
    """`solutions` exists only for a complete contraction.

    For a truncated prefix, `partial_assignments` counts compatible choices
    for the processed free cells and is NOT a Sudoku solution count.
    """
    solutions: int | None
    partial_assignments: int
    stats: OrbitFrontierStats


def contract_digit_orbits(
    puzzle: Puzzle,
    *,
    mode: OrbitMode = 'permutations',
    limits: FrontierLimits = FrontierLimits(),
    domains: Sequence[int] | None = None,
    max_cells: int | None = None,
) -> OrbitFrontierResult:
    """Contract digit-equivalent frontier signatures with exact orbit masses.

    A permutation is admitted only if it preserves each cell's candidate set.
    Therefore it acts equivariantly on both the initial state and every
    transition. A representative emits exactly the same number of transitions
    *to each target orbit* as every other state in its source orbit; multiplying
    those transition counts by its aggregate integer mass is exact.

    With `suffix-permutations`, the allowable digit symmetry can grow as
    cells are consumed: future continuations depend only on the remaining
    domains and projected used bits, not on the labels of past clues. The
    smaller group at each layer is contained in the next layer's group.

    `max_cells` is a diagnostic *prefix* limit, not a counting shortcut.
    """
    n = puzzle.side
    if puzzle.b < 1 or len(puzzle.entries) != n * n or any(
        given < 0 or given > n for given in puzzle.entries
    ):
        raise ValueError('Invalid Sudoku dimensions or clues')
    if max_cells is not None and max_cells < 0:
        raise ValueError('Prefix length must be nonnegative')
    if domains is None:
        initial = initial_domains(puzzle)
        if initial is None:
            empty = OrbitFrontierStats(1, 0, 0, 0, 0, 0, 0, 0, 0)
            return OrbitFrontierResult(0, 0, empty)
    else:
        if len(domains) != n * n:
            raise ValueError('Domain vector length differs from Sudoku')
        initial = tuple(domains)
        for cell, (mask, given) in enumerate(zip(initial, puzzle.entries)):
            if given and mask != (1 << (given - 1)):
                raise ValueError(f'Domain contradicts given at cell {cell}')
    if mode == 'suffix-permutations':
        initial_group = _symmetry_for_masks(initial, n, 'permutations')
    else:
        initial_group = symmetry_for_domains(initial, n, mode)
    units = puzzle.units()
    cell_units: list[list[int]] = [[] for _ in puzzle.entries]
    for index, cells in enumerate(units):
        for cell in cells:
            cell_units[cell].append(index)
    if any(len(indices) != 3 for indices in cell_units):
        raise ValueError('Expected exactly three units per Sudoku cell')
    base = 0
    free: list[int] = []
    options: dict[int, tuple[int, ...]] = {}
    for cell, domain in enumerate(initial):
        choices: list[int] = []
        while domain:
            bit = domain & -domain
            domain ^= bit
            digit = bit.bit_length() - 1
            candidate = sum(1 << (index * n + digit)
                            for index in cell_units[cell])
            choices.append(candidate)
        if len(choices) == 1:
            if base & choices[0]:
                empty = OrbitFrontierStats(initial_group.order, 0, 0, 0, 0, 0, 0, 0, 0)
                return OrbitFrontierResult(0, 0, empty)
            base |= choices[0]
        else:
            free.append(cell)
            options[cell] = tuple(choices)
    future = [0] * (len(free) + 1)
    for pos in range(len(free) - 1, -1, -1):
        future[pos] = future[pos + 1]
        for candidate in options[free[pos]]:
            future[pos] |= candidate
    if mode == 'suffix-permutations':
        groups = tuple(
            _symmetry_for_masks(tuple(initial[cell] for cell in free[pos:]),
                                n, 'permutations')
            for pos in range(len(free) + 1)
        )
    else:
        groups = (initial_group,) * (len(free) + 1)
    # Each group stabilizes the future domains for its layer, so each future
    # mask is invariant under the current group. The initial *base* need not
    # be invariant for suffix symmetry: it is already captured by the state.
    table = {groups[0].canonical(base & future[0]): 1}
    peak = 1
    transitions = compatible = merged = processed = 0
    budget = 160 + 2 * ((3 * n * n + 7) // 8)
    if budget > limits.max_estimated_bytes:
        raise FrontierCapacityError('Orbit estimated-byte limit')
    steps = len(free) if max_cells is None else min(max_cells, len(free))
    for pos in range(steps):
        processed += 1
        next_table: dict[int, int] = {}
        keep = future[pos + 1]
        for signature, mass in table.items():
            for candidate in options[free[pos]]:
                transitions += 1
                if transitions > limits.max_transitions:
                    raise FrontierCapacityError('Orbit transition limit')
                if signature & candidate:
                    continue
                compatible += 1
                key = groups[pos + 1].canonical((signature | candidate) & keep)
                if key in next_table:
                    next_table[key] += mass
                    merged += 1
                else:
                    size = len(next_table) + 1
                    if size > limits.max_states:
                        raise FrontierCapacityError('Orbit state limit')
                    if (len(table) + size) * budget > limits.max_estimated_bytes:
                        raise FrontierCapacityError('Orbit estimated-byte limit')
                    next_table[key] = mass
        table = next_table
        peak = max(peak, len(table))
        if not table:
            break
    total = sum(table.values())
    stats = OrbitFrontierStats(
        group_order=groups[0].order,
        free_cells=len(free),
        processed_cells=processed,
        peak_orbits=peak,
        final_orbits=len(table),
        final_raw_states=sum(groups[processed].orbit_size(state) for state in table),
        candidate_transitions=transitions,
        compatible_transitions=compatible,
        merged_transitions=merged,
        final_group_order=groups[processed].order,
    )
    return OrbitFrontierResult(
        solutions=total if processed == len(free) or not table else None,
        partial_assignments=total, stats=stats,
    )
