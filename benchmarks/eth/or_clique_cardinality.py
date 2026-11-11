"""Research-only exact cardinality-state elimination for positive-OR cliques.

A clique of constraints (xi OR xj) is satisfied iff at most one variable
is zero. Its symmetric state has two counts: no zeros and exactly one zero.
This is a special-case compact quotient, not a general circuit algorithm.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class CardinalityTrace:
    count: int
    states: tuple[tuple[int, int], ...]
    arithmetic_adds: int
    max_coefficient_bits: int
    peak_state_entries: int


def count_or_clique_cardinality(n: int) -> CardinalityTrace:
    """Exact count by quotienting assignments under variable permutations.

    After k variables, states (a,b) count assignments with zero or one zero.
    Appending a one preserves both; appending a zero moves a into b.
    Thus (a,b) -> (a,a+b), with one exact integer addition per step.
    """
    if type(n) is not int or n < 2:
        raise ValueError("n must be an integer >= 2")
    a, b = 1, 0
    states = [(a, b)]
    bits = 1
    for _ in range(n):
        a, b = a, a + b
        states.append((a, b))
        bits = max(bits, a.bit_length(), b.bit_length())
    return CardinalityTrace(
        count=a + b, states=tuple(states), arithmetic_adds=n + 1,
        max_coefficient_bits=max(bits, (a + b).bit_length()),
        peak_state_entries=2,
    )


def first_bucket_symbolic_value(remaining: tuple[int, ...]) -> int:
    """Evaluate 1 + product(x_i), the exact first induced OR-clique factor."""
    if any(x not in (0, 1) for x in remaining):
        raise ValueError("Boolean inputs required")
    return 1 + int(all(remaining))
