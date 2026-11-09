"""Pure, coefficient-free factor-scope planning.

Aji--McEliece's generalized distributive law and Dechter's bucket
elimination distinguish structural scope growth from factor arithmetic.
The same incident-union calculation is used by Boolean leaves, mode
elimination, and ETH Taylor group elimination, but their ordering
heuristics and admitted operations remain separate.

A free variable has no incident factors.  Its joined scope is the
singleton variable for bookkeeping, while callers explicitly account
for the empty product and their own free-variable multiplicity.
"""
from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass
from math import prod


@dataclass(frozen=True, slots=True)
class EliminationScope:
    """Topology for eliminating one variable; factor order is preserved."""

    variable: int
    incident: tuple[int, ...]
    joined: tuple[int, ...]
    output: tuple[int, ...]

    @property
    def is_free(self) -> bool:
        return not self.incident


def inspect_scope(
    variable: int, factor_scopes: Sequence[Sequence[int]],
) -> EliminationScope:
    """Inspect incidence and fill scope without reading coefficient values.

    The incident indices refer to the *current* factor sequence.  This
    routine never constructs a Cartesian assignment table.  Callers
    discard and replan after factor elimination because scopes change.
    """
    incident = tuple(
        index for index, scope in enumerate(factor_scopes) if variable in scope
    )
    union: set[int] = {variable}
    for index in incident:
        union.update(factor_scopes[index])
    joined = tuple(sorted(union))
    output = tuple(v for v in joined if v != variable)
    return EliminationScope(variable, incident, joined, output)



def choose_min_width(
    remaining: Iterable[int], factor_scopes: Sequence[Sequence[int]],
) -> EliminationScope:
    """Leaf min-width key, retaining free-wire priority and index ties.

    Compare candidates using only union cardinality and incidence counts.
    Materialize and sort a complete EliminationScope only for the winner.
    Constructing one dataclass and sorted scope per *candidate* caused
    measurable planner overhead without changing the chosen variable.
    """
    chosen: int | None = None
    best: tuple[int, int, int] | None = None
    for variable in remaining:
        union: set[int] = set()
        incidents = 0
        for scope in factor_scopes:
            if variable in scope:
                incidents += 1
                union.update(scope)
        # An isolated wire contributes two choices; its legacy key is -1.
        key = (len(union) - 1, incidents, variable)
        if best is None or key < best:
            best, chosen = key, variable
    if chosen is None:
        raise ValueError("Cannot eliminate from an empty variable set")
    return inspect_scope(chosen, factor_scopes)


def choose_min_domain(
    remaining: Iterable[int],
    factor_scopes: Sequence[Sequence[int]],
    domain_sizes: Sequence[int],
) -> EliminationScope:
    """ETH dense joint-domain ordering; no dense assignment tables built.

    Preserve the original (domain product, joined width, group index) key.
    For a free group the mathematical factor scope is empty and its
    product is 1, although inspect_scope records the singleton variable.
    """
    if any(type(size) is not int or size < 1 for size in domain_sizes):
        raise ValueError("Domain cardinalities must be positive integers")
    chosen: int | None = None
    best: tuple[int, int, int] | None = None
    for variable in remaining:
        union: set[int] = set()
        for scope in factor_scopes:
            if variable in scope:
                union.update(scope)
        if any(v < 0 or v >= len(domain_sizes) for v in union):
            raise ValueError("Factor scope references an invalid domain")
        key = (prod(domain_sizes[v] for v in union), len(union), variable)
        if best is None or key < best:
            best, chosen = key, variable
    if chosen is None:
        raise ValueError("Cannot eliminate from an empty variable set")
    return inspect_scope(chosen, factor_scopes)
