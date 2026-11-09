"""Optional exact #SAT oracle using pyganak, with explicit CNF semantics.

This is deliberately separate from the production contraction implementation.
The exact count includes *all declared variables*, including unused variables.
No weighted/floating-point or approximate counter is used.
"""
from __future__ import annotations

import importlib
from collections.abc import Sequence
from typing import Protocol, cast

from non_exponential_sudoku.sudoku.three_cnf import CNF


class _ExactCounter(Protocol):
    def new_vars(self, count: int) -> object: ...
    def add_clauses(self, clauses: Sequence[Sequence[int]]) -> object: ...
    def count(self) -> int: ...


class _ExactCounterFactory(Protocol):
    def __call__(self, *, verbose: int = 0, seed: int = 0) -> _ExactCounter: ...


def count_cnf(formula: CNF, *, seed: int = 0) -> int:
    """Count all models of a CNF, preserving declared-variable semantics.

    Fail closed on malformed DIMACS-like inputs. pyganak's empty-clause
    behavior on a zero-variable instance is inconsistent across instances;
    an empty clause is a contradiction by definition, so short-circuit it.
    A fresh solver is constructed per request (Ganak counts once per instance).
    """
    if type(formula.nvars) is not int or formula.nvars < 0:
        raise ValueError("nvars must be a nonnegative integer")
    clauses: list[tuple[int, ...]] = []
    for clause in formula.clauses:
        checked: list[int] = []
        for literal in clause:
            if type(literal) is not int or not 1 <= abs(literal) <= formula.nvars:
                raise ValueError("CNF literal outside declared variable range")
            checked.append(literal)
        clauses.append(tuple(checked))
    if any(not clause for clause in clauses):
        return 0
    if not clauses:
        return 1 << formula.nvars

    try:
        module = importlib.import_module("pyganak")
    except ImportError as exc:
        raise RuntimeError("Exact Ganak oracle requires optional package pyganak") from exc
    factory = cast(_ExactCounterFactory, module.Counter)
    counter = factory(seed=seed)
    counter.new_vars(formula.nvars)
    counter.add_clauses(clauses)
    result = counter.count()
    if type(result) is not int or result < 0 or result > (1 << formula.nvars):
        raise RuntimeError("Ganak returned a non-exact or out-of-range model count")
    return result
