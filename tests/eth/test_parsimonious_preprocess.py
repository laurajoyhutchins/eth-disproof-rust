"""Tseitin OR-gate and Tovey-cycle #SAT reductions."""
from __future__ import annotations

from random import Random
from importlib.util import find_spec

import pytest

from non_exponential_sudoku.eth import CNFFormula, count_bruteforce, count_ganak
from non_exponential_sudoku.eth.preprocess import ReductionLimits, reduce_width_occurrences
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def _check_bounded(formula: CNFFormula) -> None:
    assert max((len(c) for c in formula.clauses), default=0) <= 3
    counts = [0] * (formula.nvars + 1)
    for c in formula.clauses:
        for lit in c:
            counts[abs(lit)] += 1
    assert max(counts) <= 3


def test_free_bits_empty_clause_and_copy_bijection() -> None:
    fixtures = (
        CNFFormula(0, ()), CNFFormula(3, ()), CNFFormula(3, ((),)),
        CNFFormula(4, ((1, 2, 3, 4),)),
        CNFFormula(3, ((1, 2), (-1, 2), (1, -3))),
        CNFFormula(4, ((1, 2, 3, 4), (-1,), (-2, 3))),
    )
    for formula in fixtures:
        reduced = reduce_width_occurrences(formula)
        _check_bounded(reduced.formula)
        if find_spec("pyganak") is not None:
            assert count_ganak(reduced.formula) == count_bruteforce(formula)
    # x appears twice, so its original ID must not be left as a free bit.
    original = CNFFormula(2, ((1,), (-1, 2)))
    reduced = reduce_width_occurrences(original).formula
    assert count_bruteforce(original) == 1
    if find_spec("pyganak") is not None:
        assert count_ganak(reduced) == 1


def test_randomized_parsimonious_reduction_with_real_ganak() -> None:
    pytest.importorskip('pyganak')
    rng = Random(26805)
    for _ in range(65):
        n = rng.randint(0, 5)
        clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randint(0, 6)))
                        for _ in range(rng.randint(0, 4))) if n else ((),)
        f = CNFFormula(n, clauses)
        reduced = reduce_width_occurrences(f)
        _check_bounded(reduced.formula)
        assert count_ganak(reduced.formula) == count_bruteforce(f)
        assert reduce_width_occurrences(f) == reduced  # deterministic


def test_preprocessing_refuses_limits() -> None:
    formula = CNFFormula(4, ((1, 2, 3, 4),))
    with pytest.raises(CapacityError, match='variable'):
        reduce_width_occurrences(formula, limits=ReductionLimits(max_variables=4))
    with pytest.raises(CapacityError, match='clause'):
        reduce_width_occurrences(formula, limits=ReductionLimits(max_clauses=1))
    with pytest.raises(CapacityError, match='literal'):
        reduce_width_occurrences(formula, limits=ReductionLimits(max_literal_occurrences=3))
    with pytest.raises(ValueError):
        ReductionLimits(max_variables=0)
