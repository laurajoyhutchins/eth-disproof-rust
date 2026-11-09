"""Shared algebraic test helpers (not production code)."""
from __future__ import annotations
from non_exponential_sudoku.runtime.config import ModeLimits
from non_exponential_sudoku.runtime.statistics import Counters
from itertools import product
from non_exponential_sudoku.core.modes import Mode
from non_exponential_sudoku.elimination.engine import ModeEliminator
from non_exponential_sudoku.runtime.budget import CapacityError


def synthetic_modes(pairs, p):
    return [Mode(j, 0, 0, u, v, 1, (), (0,)) for j, (u, v) in enumerate(pairs)]


def exhaustive_weighted_assignments(modes, precision):
    """Independent Cartesian-product oracle for bounded test graphs only."""
    dimensions=[range(min(len(m.rows), (precision-1)//m.weight)+1) for m in modes]
    for assignment in product(*dimensions):
        if sum(m.weight * b for m, b in zip(modes, assignment)) < precision:
            yield assignment


def reference_factor_sum(modes, ring, evaluate_group):
    groups=sorted({v for m in modes for v in (m.source, m.target)})
    answer=ring.zero
    for assignment in exhaustive_weighted_assignments(modes, ring.p):
        value=ring.one
        for group in groups:
            scope=tuple(j for j,m in enumerate(modes)
                        if group in (m.source, m.target))
            value=ring.mul(value, evaluate_group(
                group,scope,tuple(assignment[j] for j in scope)))
        answer=ring.add(answer,value)
    return answer


# The solver and its independent tests use the same declared measurement shape.
ModeStats = Counters


def dp_sum(modes, ring, evaluate_group, **kwargs):
    stats=ModeStats()
    budget_fields = {field: kwargs.pop(field) for field in tuple(kwargs)
                     if field in ModeLimits.__dataclass_fields__}
    limits = ModeLimits(**budget_fields)
    answer=ModeEliminator(modes,
        {group for m in modes for group in (m.source, m.target)},
        ring,evaluate_group,stats,CapacityError,limits=limits,**kwargs).run()
    return answer,stats
