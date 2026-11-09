"""Exact conditional-expectations schedule assignment (incidence-labels lemma).

Derandomizes the manuscript's quadratic collision potential Phi and group
occupancy potential Xi.  When the lemma's *explicit hypotheses* hold,
its label load and group-size bounds follow.  For tiny inputs the same
construction is valid but the asymptotic load bound may not hold.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product

from non_exponential_sudoku.runtime.budget import CapacityError

from .cnf import CNFFormula


@dataclass(frozen=True, slots=True)
class BalanceLimits:
    max_domain_size: int = 16
    max_indicator_work: int = 2_000_000

    def __post_init__(self) -> None:
        if (type(self.max_domain_size) is not int or self.max_domain_size < 1 or
                type(self.max_indicator_work) is not int or self.max_indicator_work < 1):
            raise ValueError('balance limits must be positive integers')


@dataclass(frozen=True, slots=True)
class BalancedSchedules:
    variable_schedules: tuple[tuple[int, ...], ...]
    clause_schedules: tuple[tuple[int, ...], ...]
    initial_potential: Fraction
    final_potential: Fraction
    max_label_multiplicity: int
    max_group_size: int
    lemma_hypotheses_met: bool
    lemma_bounds_met: bool


def choose_balanced_schedules(
    formula: CNFFormula, *, r: int, Q: int,
    limits: BalanceLimits = BalanceLimits(),
) -> BalancedSchedules:
    """Derandomize Phi/[M(b+w)] + Xi/[Qn] without floating point.

    Runtime is polynomial in n, M, r**Q and the candidate count, but may be
    prohibitively expensive.  A work cap prevents hidden exhaustive search.
    This function never claims the lemma's bounds if its hypotheses fail.
    """
    if type(r) is not int or type(Q) is not int or r < 2 or Q < 1 or formula.nvars < r:
        raise ValueError('balanced schedules require nvars>=r>=2 and Q>=1')
    n, clauses = formula.nvars, formula.clauses
    M = sum(len(clause) for clause in clauses)
    K = r ** Q
    if K > limits.max_domain_size:
        raise CapacityError('ETH balancing schedule domain limit')
    active = tuple(e for e, clause in enumerate(clauses) if clause)
    estimate = (n + len(active)) * K * (M * M + Q * n * n)
    if estimate > limits.max_indicator_work:
        raise CapacityError('ETH balancing indicator work limit')
    domain = tuple(product(range(r), repeat=Q))
    a: list[tuple[int, ...] | None] = [None] * n
    # Empty-scope factors have the fixed schedule 0,..,0 per the paper.
    d: list[tuple[int, ...] | None] = [None if clause else (0,) * Q for clause in clauses]
    incidence = tuple((e, abs(lit) - 1) for e, clause in enumerate(clauses) for lit in clause)
    b = max((sum(abs(lit) == v + 1 for c in clauses for lit in c)
             for v in range(n)), default=0)
    w = max((len(c) for c in clauses), default=0)
    D = K * K
    hypotheses = bool(M >= n and b > 0 and w > 0 and
                      2 * (b + w) * D * D <= M and 2 * Q * r * r <= n)

    def equality(left: tuple[int, ...] | None,
                 right: tuple[int, ...] | None, same: bool) -> Fraction:
        if same:
            return Fraction(1)
        if left is None or right is None:
            return Fraction(1, K)
        return Fraction(int(left == right))

    def potential() -> Fraction:
        # The -M^2/D and -Q*n^2/r terms are constant under conditioning,
        # so minimizing the uncentered pair expectations is equivalent.
        phi = Fraction(0)
        for e, v in incidence:
            for f, wvar in incidence:
                phi += equality(a[v], a[wvar], v == wvar) * equality(
                    d[e], d[f], e == f)
        xi = Fraction(0)
        for t in range(Q):
            for v in range(n):
                for v2 in range(n):
                    if v == v2:
                        xi += 1
                    else:
                        left, right = a[v], a[v2]
                        if left is None or right is None:
                            xi += Fraction(1, r)
                        else:
                            xi += int(left[t] == right[t])
        # A zero-incidence input has no Phi contribution; the group
        # potential still determines a deterministic balanced assignment.
        return (phi / (M * (b + w)) if M else Fraction(0)) + xi / (Q * n)

    initial = potential()
    previous = initial
    for schedules, indices in ((a, tuple(range(n))), (d, active)):
        for index in indices:
            best: tuple[Fraction, tuple[int, ...]] | None = None
            for candidate in domain:
                schedules[index] = candidate
                score = potential()
                if best is None or score < best[0]:
                    best = (score, candidate)
            if best is None:
                raise ArithmeticError('empty balancing candidate domain')
            schedules[index] = best[1]
            if best[0] > previous:
                raise ArithmeticError('conditional expectation increased')
            previous = best[0]
    if any(v is None for v in a) or any(v is None for v in d):
        raise ArithmeticError('incomplete balancing schedules')
    variables = tuple(v for v in a if v is not None)
    factors = tuple(v for v in d if v is not None)
    loads: dict[tuple[tuple[int, int], ...], int] = {}
    for e, v in incidence:
        label = tuple((variables[v][t], factors[e][t]) for t in range(Q))
        loads[label] = loads.get(label, 0) + 1
    max_load = max(loads.values(), default=0)
    max_group = max(sum(s[t] == g for s in variables) for t in range(Q) for g in range(r))
    bounds = (max_load * D <= 2 * M and max_group * r <= 2 * n)
    if hypotheses and not bounds:
        raise ArithmeticError('conditional expectations violated lemma bounds')
    return BalancedSchedules(variables, factors, initial, previous,
                             max_load, max_group, hypotheses, bounds)
