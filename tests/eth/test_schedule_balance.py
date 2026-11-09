"""Check exact conditional expectations against independent brute score."""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from random import Random

import pytest

from non_exponential_sudoku.eth import (CNFFormula, BalanceLimits,
                                        choose_balanced_schedules,
                                        construct_auxiliary, construct_from_schedules)
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def _raw_score(f: CNFFormula, a: tuple[tuple[int, ...], ...],
               d: tuple[tuple[int, ...], ...], r: int, Q: int) -> Fraction:
    incidence = tuple((e, abs(lit) - 1) for e, clause in enumerate(f.clauses) for lit in clause)
    M = len(incidence)
    b = max((sum(v == i for _, v in incidence) for i in range(f.nvars)), default=0)
    w = max((len(c) for c in f.clauses), default=0)
    D = r ** (2 * Q)
    collision = sum((int(tuple((a[v][t], d[e][t]) for t in range(Q)) ==
                         tuple((a[v2][t], d[e2][t]) for t in range(Q)))
                     for e, v in incidence for e2, v2 in incidence))
    groups = sum(sum(int(a[v][t] == a[v2][t]) for v in range(f.nvars)
                     for v2 in range(f.nvars)) for t in range(Q))
    return ((Fraction(collision, M * (b + w)) if M else Fraction(0))
            + Fraction(groups, Q * f.nvars))


def test_exact_method_of_conditional_expectations() -> None:
    formulas = (CNFFormula(3, ((1, 2), (2, 3), (-1, 3))),
                CNFFormula(4, ((1, -2), (-3, 4))),
                CNFFormula(3, ()), CNFFormula(3, ((1, 2), ())),
                CNFFormula(4, ((1, 2, 3), (1, -3), (2, 4))))
    for f in formulas:
        result = choose_balanced_schedules(f, r=2, Q=2)
        assert result.final_potential == _raw_score(f, result.variable_schedules,
                                                     result.clause_schedules, 2, 2)
        assert result.final_potential <= result.initial_potential
        assert not result.lemma_hypotheses_met  # small instances don't meet paper inequalities
        assert result == choose_balanced_schedules(f, r=2, Q=2)
        assert all(f.clauses[e] or result.clause_schedules[e] == (0, 0)
                   for e in range(len(f.clauses)))
        aux = construct_auxiliary(r=2, Q=2, R=2)
        constructed = construct_from_schedules(f, aux, result.variable_schedules,
                                                result.clause_schedules)
        assert len(constructed.centers) == 2


def test_balancing_is_deterministic_on_random_inputs() -> None:
    rng = Random(29116)
    for _ in range(15):
        n = rng.randint(2, 5)
        f = CNFFormula(n, tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                                      for _ in range(rng.randint(0, 3)))
                                for _ in range(rng.randint(0, 3))))
        result = choose_balanced_schedules(f, r=2, Q=1)
        assert result.final_potential <= result.initial_potential
        assert result.final_potential == _raw_score(f, result.variable_schedules,
                                                     result.clause_schedules, 2, 1)


def test_balance_budget_refusals() -> None:
    f = CNFFormula(4, ((1, 2), (2, 3), (3, 4)))
    with pytest.raises(CapacityError, match='domain'):
        choose_balanced_schedules(f, r=2, Q=5)
    with pytest.raises(CapacityError, match='work'):
        choose_balanced_schedules(f, r=2, Q=2,
                                  limits=BalanceLimits(max_indicator_work=10))
    with pytest.raises(ValueError, match='nvars'):
        choose_balanced_schedules(CNFFormula(1, ((1,),)), r=2, Q=1)
