"""Exact factorized restricted Taylor summation over measured Boolean groups.

The original separated identity
   sum_y product_g sum_{x_g: M_g x_g=y_g} F_g(x_g, y)
can be regrouped exactly into a product of factors on local group masks:
each x_g determines its measured signature y_g uniquely.  Clause e
depends only on its owner group and groups with a nonzero certified
measurement coefficient.  Bucket elimination sums group masks without
enumerating all global measurement tuples.

Worst-case induced factor scope can still contain all groups; bounded
table/work limits fail closed instead of hiding exponential enumeration.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import prod
from typing import TYPE_CHECKING

from non_exponential_sudoku.runtime.budget import CapacityError

if TYPE_CHECKING:
    from .taylor import _JetValue, _TaylorEvaluator


@dataclass(slots=True)
class _Factor:
    scope: tuple[int, ...]
    values: dict[tuple[int, ...], _JetValue]


def eliminate_restricted(
    evaluator: _TaylorEvaluator, E: tuple[int, ...],
    corrections: tuple[tuple[_JetValue, ...], ...],
) -> _JetValue:
    """Exact bounded variable elimination over Boolean group masks."""
    cert = evaluator.certificate
    design = cert.design
    groups = design.groups
    arithmetic = evaluator.arithmetic
    order = evaluator.order
    forced = set(E)
    free_indices = [tuple(i for i, v in enumerate(group) if v not in forced)
                    for group in groups]
    fixed = [sum(1 << i for i, v in enumerate(group) if v in forced)
             for group in groups]
    domain_size = tuple(1 << len(free) for free in free_indices)
    masks: dict[int, tuple[int, ...]] = {}
    signatures: dict[int, dict[int, tuple[int, ...]]] = {}

    def valid_masks(g: int) -> tuple[int, ...]:
        if g not in masks:
            if domain_size[g] > evaluator.limits.max_factor_entries:
                raise CapacityError('ETH Taylor factor domain entry limit')
            masks[g] = tuple(
                fixed[g] | sum(1 << free_indices[g][i]
                               for i in range(len(free_indices[g]))
                               if subset & (1 << i))
                for subset in range(domain_size[g])
            )
        return masks[g]

    def measured(g: int, mask: int) -> tuple[int, ...]:
        if g not in signatures:
            signatures[g] = {}
        if mask not in signatures[g]:
            signatures[g][mask] = tuple(
                sum(coef for j, coef in enumerate(row) if mask & (1 << j))
                for row in design.matrices[g]
            )
        return signatures[g][mask]

    def charge(work: int, scope: tuple[int, ...]) -> None:
        evaluator.factor_assignments += work
        if evaluator.factor_assignments > evaluator.limits.max_factor_work:
            raise CapacityError('ETH Taylor factor work limit')
        evaluator.factor_scope_peak = max(evaluator.factor_scope_peak, len(scope))

    def record(factors: list[_Factor]) -> None:
        if not factors:
            return
        largest = max(len(f.values) for f in factors)
        evaluator.factor_entries_peak = max(evaluator.factor_entries_peak, largest)
        if largest > evaluator.limits.max_factor_entries:
            raise CapacityError('ETH Taylor factor table entry limit')
        if sum(len(f.values) for f in factors) > evaluator.limits.max_factor_total_entries:
            raise CapacityError('ETH Taylor total factor entry limit')

    factors: list[_Factor] = []
    for e, clause in enumerate(evaluator.formula.clauses):
        owner = design.clause_groups[e]
        foreign_groups = {
            g for occurrence in cert.occurrences[e]
            for g, weights in enumerate(occurrence.lambda_by_group)
            if any(weights)
        }
        scope = tuple(sorted(foreign_groups | {owner}))
        charge(prod(domain_size[g] for g in scope), scope)
        values: dict[tuple[int, ...], _JetValue] = {}
        for assignment in product(*(valid_masks(g) for g in scope)):
            evaluator.tried += 1
            owner_mask = assignment[scope.index(owner)]
            bits = tuple((owner_mask >> j) & 1
                         for j in range(len(groups[owner])))
            unsatisfied = evaluator.one
            for literal, occurrence, correction in zip(
                clause, cert.occurrences[e], corrections[e],
            ):
                base = sum(
                    (coef for j, coef in enumerate(occurrence.local) if bits[j]),
                    Fraction(0),
                )
                for h, weights in enumerate(occurrence.lambda_by_group):
                    if any(weights):
                        signature = measured(h, assignment[scope.index(h)])
                        base += sum(
                            (weight * observed
                             for weight, observed in zip(weights, signature)),
                            Fraction(0),
                        )
                linear = arithmetic.add(arithmetic.constant(base, order), correction)
                false_literal = (
                    arithmetic.sub(evaluator.one, linear) if literal > 0 else linear
                )
                unsatisfied = arithmetic.mul(unsatisfied, false_literal)
            value = arithmetic.sub(evaluator.one, unsatisfied)
            evaluator.clause_evaluations += 1
            if not arithmetic.is_zero(value):
                values[assignment] = value
                evaluator.matching += 1
                if len(values) > evaluator.limits.max_factor_entries:
                    raise CapacityError('ETH Taylor factor table entry limit')
        factors.append(_Factor(scope, values))
        record(factors)
        if not values:
            return evaluator.zero

    remaining = set(range(len(groups)))
    result = evaluator.one
    while remaining:
        def union_scope(g: int) -> tuple[int, ...]:
            return tuple(sorted({h for factor in factors if g in factor.scope
                                 for h in factor.scope}))

        # Minimize the exact domain product of the next induced bucket.
        group = min(remaining, key=lambda g: (
            prod(domain_size[h] for h in union_scope(g)),
            len(union_scope(g)), g,
        ))
        scope = union_scope(group)
        remaining.remove(group)
        evaluator.factor_eliminations += 1
        if not scope:
            # An isolated group needs no explicit enumeration.
            result = arithmetic.mul(
                result, arithmetic.constant(domain_size[group], order))
            continue

        attached = [factor for factor in factors if group in factor.scope]
        factors = [factor for factor in factors if group not in factor.scope]
        charge(prod(domain_size[h] for h in scope), scope)
        output_scope = tuple(g for g in scope if g != group)
        output: dict[tuple[int, ...], _JetValue] = {}
        for assignment in product(*(valid_masks(h) for h in scope)):
            evaluator.tried += 1
            value = evaluator.one
            for factor in attached:
                key = tuple(assignment[scope.index(h)] for h in factor.scope)
                entry = factor.values.get(key)
                if entry is None:
                    break
                value = arithmetic.mul(value, entry)
                if arithmetic.is_zero(value):
                    break
            else:
                key = tuple(assignment[scope.index(h)] for h in output_scope)
                previous = output.get(key)
                output[key] = (
                    arithmetic.add(previous, value) if previous is not None else value
                )
                if len(output) > evaluator.limits.max_factor_entries:
                    raise CapacityError('ETH Taylor factor table entry limit')
        output = {key: value for key, value in output.items()
                  if not arithmetic.is_zero(value)}
        factors.append(_Factor(output_scope, output))
        record(factors)
        if not output:
            return evaluator.zero

    for factor in factors:
        if factor.scope:
            raise ArithmeticError('factor elimination left unbound groups')
        terminal = factor.values.get(())
        if terminal is None:
            return evaluator.zero
        result = arithmetic.mul(result, terminal)
    return result
