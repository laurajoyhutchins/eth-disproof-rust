"""Optional Ganak exact #SAT reference/benchmark adapter, not an ETH path.

This adapter uses the packaged `pyganak.Counter` interface and declares
unused variables explicitly. It is not a replacement for the paper's ETH
construction. The binding does not expose every CLI caching/certification
option; its integer results are therefore independent differential evidence,
not a mathematical proof or a deterministic certificate of exact counting.
"""
from __future__ import annotations

from importlib import import_module

from .backends import BackendUnavailableError
from .cnf import CNFFormula
from non_exponential_sudoku.runtime.budget import CapacityError


def count_ganak(
    formula: CNFFormula, *, seed: int = 0, max_variables: int = 100_000,
) -> int:
    """Count with installed pyganak, preserving the declared Boolean width.

    Trivial identities are handled here to avoid differences in native binding
    treatment of contradictory zero-variable CNFs. Never falls back to search.
    """
    if type(seed) is not int or seed < 0 or seed >= (1 << 64):
        raise ValueError('seed must be a uint64 integer')
    if type(max_variables) is not int or max_variables < 0:
        raise ValueError('max_variables must be a nonnegative integer')
    if formula.nvars > max_variables or formula.nvars >= (1 << 32):
        raise CapacityError('Ganak declared-variable limit')
    if formula.clauses == ((),):
        return 0
    if not formula.clauses:
        return 1 << formula.nvars
    try:
        module = import_module('pyganak')
    except ImportError as exc:
        raise BackendUnavailableError(
            'Ganak backend requires pyganak; install with the eth-ganak extra'
        ) from exc
    counter = module.Counter(seed=seed)
    counter.new_vars(formula.nvars)
    counter.add_clauses([list(clause) for clause in formula.clauses])
    count: object = counter.count()
    if type(count) is not int or not 0 <= count <= (1 << formula.nvars):
        raise ArithmeticError('Ganak returned an invalid exact model count')
    return count
