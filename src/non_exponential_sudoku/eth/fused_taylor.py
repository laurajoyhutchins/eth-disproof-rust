"""Exact truncated Boolean-difference fusion by sparse polynomial factors.

For each Boolean assignment x, Möbius summation of restricted differences
over (E,U), U subset E subset support(x), reconstructs the substitution
P_e,v(t+z)*x_v. Terms with |E|>q vanish modulo z**(q+1) because every
Delta P_e,v(t+z) is divisible by z. Therefore the Taylor coefficients equal

    [z**<=q] sum_{x in {0,1}^n} prod_{clauses e}
        (1 - prod_{literals ell in e} false_ell(P_e,ell(t+z) dot x)).

We eliminate factors over *original Boolean variables* rather than enumerating
the 3**n finite differences or the full Boolean cube. This is classical
variable elimination on the exact deformation polynomial and can have
exponential induced width. It does not establish the ETH theorem or a
uniform non-refusal guarantee. The original separated-difference algorithms
remain independent mathematical oracles and the default implementation.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import TYPE_CHECKING

from non_exponential_sudoku.runtime.budget import CapacityError

if TYPE_CHECKING:
    from .polynomial import ReplacementSystem
    from .taylor import _JetValue, _TaylorEvaluator


@dataclass(slots=True)
class _Factor:
    scope: tuple[int, ...]
    values: dict[tuple[int, ...], _JetValue]


def contract_fused_taylor(
    evaluator: _TaylorEvaluator, replacements: ReplacementSystem,
) -> _JetValue:
    """Compute a complete certified Taylor jet with no E/U-pair loop.

    The measurement certificate is independently checked by the calling
    evaluator. Factors use the *full polynomial replacement support*, not
    only the rowspace at an interpolation center.
    """
    formula = evaluator.formula
    arithmetic = evaluator.arithmetic
    center = evaluator.certificate.center
    order = evaluator.order
    n = formula.nvars

    def charge(scope: tuple[int, ...]) -> None:
        width = len(scope)
        evaluator.factor_scope_peak = max(evaluator.factor_scope_peak, width)
        # Test against the explicit entry/work cap before materializing 2**width.
        if width > evaluator.limits.max_factor_entries.bit_length():
            raise CapacityError('ETH Taylor fused factor entry limit')
        if width > evaluator.limits.max_factor_work.bit_length():
            raise CapacityError('ETH Taylor fused factor work limit')
        work = 1 << width
        if work > evaluator.limits.max_factor_entries:
            raise CapacityError('ETH Taylor fused factor entry limit')
        evaluator.factor_assignments += work
        if evaluator.factor_assignments > evaluator.limits.max_factor_work:
            raise CapacityError('ETH Taylor fused factor work limit')

    def record(factors: list[_Factor]) -> None:
        largest = max((len(f.values) for f in factors), default=0)
        evaluator.factor_entries_peak = max(evaluator.factor_entries_peak, largest)
        if largest > evaluator.limits.max_factor_entries:
            raise CapacityError('ETH Taylor fused factor table entry limit')
        if sum(len(f.values) for f in factors) > evaluator.limits.max_factor_total_entries:
            raise CapacityError('ETH Taylor fused total factor entry limit')

    factors: list[_Factor] = []
    for e, clause in enumerate(formula.clauses):
        # P(t+z) = P(t) + (P(t+z)-P(t)), using the evaluator's already
        # checked, exact shifted coefficients; no repeated Horner pass.
        occurrence_jets: list[tuple[_JetValue, ...]] = []
        active: set[int] = set()
        for form, shifts in zip(replacements.clauses[e], evaluator.shifts[e]):
            values: list[_JetValue] = []
            for index, (coefficient, delta) in enumerate(zip(form.coefficients, shifts)):
                value = arithmetic.add(
                    arithmetic.constant(coefficient.evaluate(center), order), delta)
                values.append(value)
                if not arithmetic.is_zero(value):
                    active.add(index)
            occurrence_jets.append(tuple(values))

        scope = tuple(sorted(active))
        charge(scope)
        table: dict[tuple[int, ...], _JetValue] = {}
        for assignment in product((0, 1), repeat=len(scope)):
            selected = tuple(scope[j] for j, bit in enumerate(assignment) if bit)
            unsatisfied = evaluator.one
            for literal, occurrence in zip(clause, occurrence_jets):
                linear = evaluator.zero
                for index in selected:
                    linear = arithmetic.add(linear, occurrence[index])
                false_literal = (arithmetic.sub(evaluator.one, linear)
                                 if literal > 0 else linear)
                unsatisfied = arithmetic.mul(unsatisfied, false_literal)
            clause_value = arithmetic.sub(evaluator.one, unsatisfied)
            evaluator.clause_evaluations += 1
            evaluator.tried += 1
            if not arithmetic.is_zero(clause_value):
                table[assignment] = clause_value
                evaluator.matching += 1
        factors.append(_Factor(scope, table))
        record(factors)
        if not table:
            return evaluator.zero

    result = evaluator.one
    remaining = set(range(n))
    while remaining:
        def union_scope(variable: int) -> tuple[int, ...]:
            return tuple(sorted({
                other for factor in factors if variable in factor.scope
                for other in factor.scope
            }))

        variable = min(remaining, key=lambda index: (
            len(union_scope(index)), index,
        ))
        scope = union_scope(variable)
        remaining.remove(variable)
        evaluator.factor_eliminations += 1
        if not scope:
            result = arithmetic.mul(result, arithmetic.constant(2, order))
            continue

        charge(scope)
        attached = [factor for factor in factors if variable in factor.scope]
        factors = [factor for factor in factors if variable not in factor.scope]
        out_scope = tuple(index for index in scope if index != variable)
        out_table: dict[tuple[int, ...], _JetValue] = {}
        positions = {index: pos for pos, index in enumerate(scope)}
        for assignment in product((0, 1), repeat=len(scope)):
            value = evaluator.one
            for factor in attached:
                key = tuple(assignment[positions[index]] for index in factor.scope)
                entry = factor.values.get(key)
                if entry is None:
                    break
                value = arithmetic.mul(value, entry)
                if arithmetic.is_zero(value):
                    break
            else:
                key = tuple(assignment[positions[index]] for index in out_scope)
                prior = out_table.get(key)
                out_table[key] = (
                    arithmetic.add(prior, value) if prior is not None else value)
            evaluator.tried += 1
        out_table = {
            key: value for key, value in out_table.items()
            if not arithmetic.is_zero(value)
        }
        factors.append(_Factor(out_scope, out_table))
        record(factors)
        if not out_table:
            return evaluator.zero

    for factor in factors:
        if factor.scope:
            raise ArithmeticError('ETH fused Taylor left unbound variables')
        terminal = factor.values.get(())
        if terminal is None:
            return evaluator.zero
        result = arithmetic.mul(result, terminal)
    return result
