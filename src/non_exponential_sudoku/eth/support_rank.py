"""Exact all-parameter boundary-rank certificates for CNF deformations.

A clause of the deformed product depends only on variables whose
replacement coefficient POLYNOMIALS are not identically zero. These
supports do not require evaluating a particular interpolation center.

For a cut L|R, move local-only clause factors to their own side.
The remaining crossing factors touch only B_L subset L and B_R
subset R. Expanding over assignments of the smaller boundary set
yields <= 2**min(|B_L|, |B_R|) separated terms over Q[T], including
for every rational center and after truncation over Q[z]/z^(q+1).

This is a certified UPPER bound, not a measured rank or a bound on
the cost of discovering an optimal variable order. The finite
subset-DP oracle is deliberately exponential in n.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from non_exponential_sudoku.runtime.budget import CapacityError

from .cnf import CNFFormula
from .polynomial import (
    Polynomial, Rational, ReplacementSystem, _exact_fraction,
    clause_satisfaction_polynomial,
)
from .unfolding_rank import (
    RankLimits, _ExactBudget, _assignment_masks, _matrix_rank,
)


@dataclass(frozen=True, slots=True)
class SupportRankLimits:
    """Finite subset-optimization budget, separate from counting budgets."""

    max_variables: int = 12
    max_subsets: int = 1 << 12
    max_support_checks: int = 200_000

    def __post_init__(self) -> None:
        for name in ("max_variables", "max_subsets", "max_support_checks"):
            val = getattr(self, name)
            if type(val) is not int or val < (0 if name == "max_variables" else 1):
                raise ValueError(f"{name} must be a bounded nonnegative/positive integer")


@dataclass(frozen=True, slots=True)
class CutSupportBound:
    left_variables: tuple[int, ...]
    right_variables: tuple[int, ...]
    boundary_left: int
    boundary_right: int
    rank_upper: int
    crossing_factors: int


@dataclass(frozen=True, slots=True)
class UniformSupportOrder:
    variable_order: tuple[int, ...]
    peak_rank_upper: int
    upper_rank_per_cut: tuple[int, ...]
    cuts_examined: int
    polynomial_terms_inspected: int
    support_checks: int
    interpretation: str = "upper bound valid at all T, not a measured optimum rank"


@dataclass(frozen=True, slots=True)
class CoefficientRank:
    """Explicit rational rank of coefficient [z**order] F(center+z)."""

    center: Fraction
    order: int
    rank: int
    matrix_rows: int
    matrix_columns: int
    exact_rational_operations: int
    max_coefficient_bits: int


def polynomial_clause_supports(
    formula: CNFFormula,
    replacements: ReplacementSystem | None = None,
) -> tuple[int, ...]:
    """Union of non-identically-zero polynomial variables in each clause.

    The result is valid over Q[T], including at algebraic exceptional
    centers where some coefficients evaluate to zero. T-autonomous.
    """
    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    replacements.validate(formula)
    masks: list[int] = []
    for occurrences in replacements.clauses:
        mask = 0
        for form in occurrences:
            for i, poly in enumerate(form.coefficients):
                if any(poly.coefficients):
                    mask |= 1 << i
        masks.append(mask)
    return tuple(masks)


def polynomial_cut_bound(
    clause_supports: Sequence[int], nvars: int,
    left_variables: tuple[int, ...],
) -> CutSupportBound:
    if type(nvars) is not int or nvars < 0:
        raise ValueError("nvars must be nonnegative")
    if (not isinstance(left_variables, tuple)
            or any(type(i) is not int or i < 0 or i >= nvars
                   for i in left_variables)
            or len(set(left_variables)) != len(left_variables)):
        raise ValueError("left_variables must be unique declared indices")
    full = (1 << nvars) - 1
    if any(type(edge) is not int or edge < 0 or edge & ~full
           for edge in clause_supports):
        raise ValueError("clause supports must be Boolean bitmasks inside nvars")
    left = sum(1 << i for i in left_variables)
    right = full ^ left
    left_boundary = right_boundary = crosses = 0
    for edge in clause_supports:
        a, b = edge & left, edge & right
        if a and b:
            crosses += 1
            left_boundary |= a
            right_boundary |= b
    return CutSupportBound(
        left_variables=left_variables,
        right_variables=tuple(i for i in range(nvars) if right & (1 << i)),
        boundary_left=left_boundary.bit_count(),
        boundary_right=right_boundary.bit_count(),
        rank_upper=1 << min(left_boundary.bit_count(), right_boundary.bit_count()),
        crossing_factors=crosses,
    )


def uniform_support_profile(
    formula: CNFFormula, replacements: ReplacementSystem | None = None, *,
    variable_order: Sequence[int],
) -> tuple[CutSupportBound, ...]:
    """Certify an existing variable order without Boolean/subset enumeration.

    The computation scans each clause support at each of n-1 cuts.
    This is O(n*m) set/bitmask operations after reading polynomial
    coefficient supports, *not* an efficient best-order search.
    """
    order = tuple(variable_order)
    if (len(order) != formula.nvars
            or any(type(i) is not int for i in order)
            or set(order) != set(range(formula.nvars))):
        raise ValueError("variable_order must be a permutation of all variables")
    supports = polynomial_clause_supports(formula, replacements)
    return tuple(
        polynomial_cut_bound(supports, formula.nvars, order[:i])
        for i in range(1, formula.nvars)
    )


def minimax_uniform_support_order(
    formula: CNFFormula, replacements: ReplacementSystem | None = None, *,
    limits: SupportRankLimits = SupportRankLimits(),
) -> UniformSupportOrder:
    """Minimize the *uniform support upper bound*, not exact tensor rank.

    B(S)=min_{v in S} max(B(S\\v),U(S)); the full-set boundary is
    excluded. This is a correct upper bound on the best exact TT bond
    rank for every center, but can be arbitrarily loose.
    """
    if not isinstance(limits, SupportRankLimits):
        raise TypeError("limits must be SupportRankLimits")
    n = formula.nvars
    if n > limits.max_variables:
        raise CapacityError("ETH uniform support variable limit")
    number_cuts = max(0, (1 << n) - 2)
    if number_cuts > limits.max_subsets:
        raise CapacityError("ETH uniform support subset limit")
    supports = polynomial_clause_supports(formula, replacements)
    total_work = number_cuts * len(supports)
    if total_work > limits.max_support_checks:
        raise CapacityError("ETH uniform support check work limit")
    full = (1 << n) - 1
    uppers: dict[int, int] = {}
    for subset in range(1, full):
        cut = tuple(i for i in range(n) if subset & (1 << i))
        uppers[subset] = polynomial_cut_bound(supports, n, cut).rank_upper

    best: dict[int, tuple[int, tuple[int, ...]]] = {0: (1, ())}
    for subset in range(1, full + 1):
        candidates = []
        for variable in range(n):
            if subset & (1 << variable):
                previous, prefix = best[subset ^ (1 << variable)]
                candidates.append(
                    (max(previous, uppers.get(subset, 1)), prefix + (variable,))
                )
        best[subset] = min(candidates)
    optimum, order = best[full]
    prefix_mask = 0
    profile: list[int] = []
    for variable in order[:-1]:
        prefix_mask |= 1 << variable
        profile.append(uppers[prefix_mask])

    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    # Count all retained nonzero coefficient terms, not just polynomial
    # objects, to ground the cost of extracting the support certificate.
    inspected = sum(
        sum(coef != 0 for coef in poly.coefficients)
        for forms in replacements.clauses for form in forms
        for poly in form.coefficients
    )
    return UniformSupportOrder(
        variable_order=order, peak_rank_upper=optimum,
        upper_rank_per_cut=tuple(profile),
        cuts_examined=number_cuts,
        polynomial_terms_inspected=inspected,
        support_checks=total_work,
    )


def coefficient_unfolding_rank(
    formula: CNFFormula, replacements: ReplacementSystem | None = None, *,
    center: Rational, order: int, left_variables: tuple[int, ...],
    limits: RankLimits = RankLimits(),
) -> CoefficientRank:
    """Bounded *independent* Boolean-cube oracle for a Taylor coefficient.

    This deliberately enumerates assignments and constructs the exact
    coefficient matrix. Do NOT use it in production or claim it is
    efficient. It checks the predicted (order+1)*U bound for tests.
    """
    point = _exact_fraction(center)
    if type(order) is not int or order < 0:
        raise ValueError("Taylor coefficient order must be nonnegative")
    n = formula.nvars
    if n > limits.max_variables or (1 << n) > limits.max_cells:
        raise CapacityError("ETH Taylor rank matrix cell limit")
    if (not isinstance(left_variables, tuple)
            or any(type(i) is not int or not 0 <= i < n for i in left_variables)
            or len(set(left_variables)) != len(left_variables)):
        raise ValueError("invalid Taylor coefficient cut")
    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    replacements.validate(formula)
    budget = _ExactBudget(limits)
    budget.check(point)
    left_set = set(left_variables)
    right = tuple(i for i in range(n) if i not in left_set)
    row_masks = _assignment_masks(left_variables)
    col_masks = _assignment_masks(right)
    matrix: list[list[Fraction]] = []
    for a in row_masks:
        row: list[Fraction] = []
        for b in col_masks:
            assignment = a | b
            product = Polynomial.constant(1)
            for clause, forms in zip(formula.clauses, replacements.clauses):
                factor = clause_satisfaction_polynomial(clause, forms, assignment)
                jet = factor.taylor(point, order)
                budget.charge()
                product = (product * jet).truncate(order)
                for coefficient in product.coefficients:
                    budget.check(coefficient)
            row.append(
                product.coefficients[order] if order < len(product.coefficients)
                else Fraction(0)
            )
        matrix.append(row)
    rank = _matrix_rank(matrix, budget)
    return CoefficientRank(
        center=point, order=order, rank=rank,
        matrix_rows=len(row_masks), matrix_columns=len(col_masks),
        exact_rational_operations=budget.operations,
        max_coefficient_bits=budget.max_bits,
    )
