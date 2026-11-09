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
    union = (
        set().union(*(factor_scopes[index] for index in incident))
        if incident else {variable}
    )
    joined = tuple(sorted(union))
    output = tuple(v for v in joined if v != variable)
    return EliminationScope(variable, incident, joined, output)


def choose_min_width(
    remaining: Iterable[int], factor_scopes: Sequence[Sequence[int]],
) -> EliminationScope:
    """Leaf min-width key, including its historical free-wire priority.

    This precisely preserves the original key
    `(len(joined union)-1, incident factor count, wire index)`
    where an isolated wire had an empty union and therefore key -1.
    """
    choices = tuple(inspect_scope(var, factor_scopes) for var in remaining)
    if not choices:
        raise ValueError("Cannot eliminate from an empty variable set")
    return min(
        choices,
        key=lambda step: (
            len(step.output) if step.incident else -1,
            len(step.incident),
            step.variable,
        ),
    )


def choose_min_domain(
    remaining: Iterable[int],
    factor_scopes: Sequence[Sequence[int]],
    domain_sizes: Sequence[int],
) -> EliminationScope:
    """ETH's dense joint-domain ordering, not a sparse-state work bound.

    An isolated group has no factors, so its historical union is empty
    and the sort key is (1, 0, group).  Domain products are arbitrary
    precision Python integers; no factor table is allocated here.
    """
    if any(type(size) is not int or size < 1 for size in domain_sizes):
        raise ValueError("Domain cardinalities must be positive integers")
    choices = tuple(inspect_scope(var, factor_scopes) for var in remaining)
    if not choices:
        raise ValueError("Cannot eliminate from an empty variable set")
    if any(var < 0 or var >= len(domain_sizes) for step in choices
           for var in step.joined):
        raise ValueError("Factor scope references an invalid domain")
    return min(
        choices,
        key=lambda step: (
            prod(domain_sizes[var] for var in step.joined) if step.incident else 1,
            len(step.joined) if step.incident else 0,
            step.variable,
        ),
    )
