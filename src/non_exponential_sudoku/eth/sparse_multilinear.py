"""Exact sparse multilinear contraction of a truncated CNF deformation.

Work in Q[z]/(z**(q+1))[x_1,...,x_n]/(x_i**2-x_i). A monomial is a
Boolean-variable subset encoded as an integer mask. Each literal's deformed
linear form has degree one in x, so a width-k clause begins with polynomial
degree at most k even if its coefficient support spans all n variables.

Unlike an explicit 2**w Boolean factor table, sparse monomials are charged
as actually materialized. Products can nevertheless fill all 2**n monomials.
Fail closed on support/work/jet-bit caps. This is a separate classical
algebraic counting algorithm, not the paper's ETH complexity theorem.
"""
from __future__ import annotations

from typing import TYPE_CHECKING

from non_exponential_sudoku.runtime.budget import CapacityError

if TYPE_CHECKING:
    from .polynomial import ReplacementSystem
    from .taylor import _JetValue, _TaylorEvaluator


def contract_multilinear(
    evaluator: _TaylorEvaluator, replacements: ReplacementSystem,
) -> _JetValue:
    """Return the exact Taylor jet of the original deformation polynomial.

    Multiplication uses x^A * x^B = x^(A union B). After multiplying all
    clause polynomials, sum_x x^A = 2**(n-|A|), with no Boolean-cube loop.
    """
    arithmetic = evaluator.arithmetic
    zero, one = evaluator.zero, evaluator.one
    limit = evaluator.limits
    n = evaluator.formula.nvars
    center = evaluator.certificate.center

    def check_support(values: dict[int, _JetValue]) -> dict[int, _JetValue]:
        if len(values) > limit.max_factor_entries:
            raise CapacityError("ETH multilinear support entry limit")
        evaluator.multilinear_support_peak = max(
            evaluator.multilinear_support_peak, len(values),
        )
        return values

    def multiply(
        left: dict[int, _JetValue], right: dict[int, _JetValue],
    ) -> dict[int, _JetValue]:
        # Bound the simultaneous input and output dictionaries, not just
        # the size of the final result. These counts are retained entries,
        # not an assertion about native allocation or resident bytes.
        input_entries = len(left) + len(right)
        if input_entries > limit.max_factor_total_entries:
            raise CapacityError("ETH multilinear total factor entry limit")
        operations = len(left) * len(right)
        # Check before constructing the Cartesian product. An explicit cap
        # is not an asymptotic result, and a refusal is not a zero count.
        if operations > limit.max_factor_work - evaluator.multilinear_term_products:
            raise CapacityError("ETH multilinear term-product work limit")
        evaluator.multilinear_term_products += operations
        answer: dict[int, _JetValue] = {}
        for left_mask, left_jet in left.items():
            for right_mask, right_jet in right.items():
                product = arithmetic.mul(left_jet, right_jet)
                if arithmetic.is_zero(product):
                    continue
                key = left_mask | right_mask
                earlier = answer.get(key)
                combined = (
                    arithmetic.add(earlier, product)
                    if earlier is not None else product
                )
                if arithmetic.is_zero(combined):
                    answer.pop(key, None)
                else:
                    answer[key] = combined
                    if len(answer) > limit.max_factor_entries:
                        raise CapacityError("ETH multilinear support entry limit")
                    if input_entries + len(answer) > limit.max_factor_total_entries:
                        raise CapacityError("ETH multilinear total factor entry limit")
        return check_support(answer)

    def one_minus(
        polynomial: dict[int, _JetValue],
    ) -> dict[int, _JetValue]:
        negative = {
            mask: arithmetic.sub(zero, jet) for mask, jet in polynomial.items()
        }
        previous = negative.get(0)
        constant = (arithmetic.add(one, previous)
                    if previous is not None else one)
        if arithmetic.is_zero(constant):
            negative.pop(0, None)
        else:
            negative[0] = constant
        return check_support(negative)

    total: dict[int, _JetValue] = {0: one}
    check_support(total)
    for clause, forms, shifts in zip(
        evaluator.formula.clauses, replacements.clauses, evaluator.shifts,
    ):
        unsatisfied: dict[int, _JetValue] = {0: one}
        for literal, form, shifted in zip(clause, forms, shifts):
            linear: dict[int, _JetValue] = {}
            for index, (polynomial, delta) in enumerate(
                zip(form.coefficients, shifted)
            ):
                constant = polynomial.evaluate(center)
                if arithmetic.is_zero(delta) and constant == 0:
                    continue
                full = arithmetic.add(
                    arithmetic.constant(constant, evaluator.order), delta,
                )
                if not arithmetic.is_zero(full):
                    linear[1 << index] = full
            false_literal = one_minus(linear) if literal > 0 else linear
            unsatisfied = multiply(unsatisfied, false_literal)
            if not unsatisfied:
                break
        clause_poly = one_minus(unsatisfied)
        total = multiply(total, clause_poly)
        if not total:
            return zero

    # The symbolic sum over {0,1}^n is a linear functional on the
    # multilinear basis. Charge output integer bit size before 2**n.
    if n + 1 > limit.max_coefficient_bits:
        raise CapacityError("ETH multilinear Boolean-sum bit limit")
    result = zero
    for mask, jet in total.items():
        multiplicity = arithmetic.constant(1 << (n - mask.bit_count()),
                                          evaluator.order)
        result = arithmetic.add(result, arithmetic.mul(jet, multiplicity))
    return result
