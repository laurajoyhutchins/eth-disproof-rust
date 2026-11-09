"""Exact bounded matrix-unfolding ranks for deformed Boolean CNF functions.

For a chosen partition L|R, an evaluation tensor f(x_L,x_R) has exact
separation rank rank_Q(M). Any representation
    f(x_L,x_R) = sum_{j=1}^D a_j(x_L) b_j(x_R)
needs D >= rank_Q(M). Conversely a rank factorization achieves equality.

A tensor train in a specified variable order must have bond dimensions at
least these unfolding ranks. This is NOT an unconditional lower bound for
exact counting or all variable orders. The diagnostic deliberately enumerates
the full Boolean cube and is never called by the production solver.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from non_exponential_sudoku.runtime.budget import CapacityError

from .cnf import CNFFormula
from .polynomial import (
    ONE, ZERO, Polynomial, Rational, ReplacementForm, ReplacementSystem,
    _exact_fraction,
)


@dataclass(frozen=True, slots=True)
class RankLimits:
    """Explicit exponential-oracle budgets, not runtime solver parameters."""

    max_variables: int = 12
    max_cells: int = 1 << 12
    max_rational_operations: int = 4_000_000
    max_coefficient_bits: int = 4096

    def __post_init__(self) -> None:
        for name in (
            "max_variables", "max_cells", "max_rational_operations",
            "max_coefficient_bits",
        ):
            value = getattr(self, name)
            if type(value) is not int or value < (0 if name == "max_variables" else 1):
                raise ValueError(f"{name} must be a nonnegative/positive integer")


@dataclass(frozen=True, slots=True)
class UnfoldingRank:
    """Exact rank of the full deformation tensor across one specified cut."""

    center: Fraction
    left_variables: tuple[int, ...]
    right_variables: tuple[int, ...]
    matrix_rows: int
    matrix_columns: int
    matrix_cells: int
    rank: int
    boundary_rank_upper: int
    left_boundary_size: int
    right_boundary_size: int
    total_value: Fraction
    rational_operations: int
    max_coefficient_bits: int


@dataclass(frozen=True, slots=True)
class MinimaxOrdering:
    """Best maximum exact cut rank among all orderings of a small tensor."""

    variable_order: tuple[int, ...]
    peak_rank: int
    cut_ranks: tuple[int, ...]
    cuts_checked: int
    charged_rational_operations: int
    max_coefficient_bits: int


class _ExactBudget:
    def __init__(self, limits: RankLimits) -> None:
        self.limits = limits
        self.operations = 0
        self.max_bits = 0

    def check(self, value: Fraction) -> Fraction:
        bits = max(value.numerator.bit_length(), value.denominator.bit_length())
        self.max_bits = max(bits, self.max_bits)
        if bits > self.limits.max_coefficient_bits:
            raise CapacityError("ETH unfolding rank rational coefficient bit limit")
        return value

    def charge(self) -> None:
        self.operations += 1
        if self.operations > self.limits.max_rational_operations:
            raise CapacityError("ETH unfolding rank rational operations limit")

    def add(self, a: Fraction, b: Fraction) -> Fraction:
        self.charge()
        return self.check(a + b)

    def sub(self, a: Fraction, b: Fraction) -> Fraction:
        self.charge()
        return self.check(a - b)

    def mul(self, a: Fraction, b: Fraction) -> Fraction:
        self.charge()
        return self.check(a * b)

    def div(self, a: Fraction, b: Fraction) -> Fraction:
        self.charge()
        return self.check(a / b)


def crossing_pair_witness(pairs: int) -> tuple[CNFFormula, ReplacementSystem]:
    """Explicit family with width-one clauses and order-sensitive rank.

    Clause i is x_i. Its replacement is x_i + T*x_(k+i). Thus at T=0
    it equals the original CNF and has rank one across x|y; at T != 0
    the exact x|y evaluation matrix has rank 2**k.
    """
    if type(pairs) is not int or pairs < 1:
        raise ValueError("pairs must be a positive integer")
    n = 2 * pairs
    formula = CNFFormula(n, tuple((i + 1,) for i in range(pairs)))
    time = Polynomial.variable()
    replacements = ReplacementSystem(tuple(
        (ReplacementForm(tuple(
            ONE if j == i else time if j == pairs + i else ZERO
            for j in range(n)
        )),)
        for i in range(pairs)
    ))
    replacements.validate(formula)
    return formula, replacements


def _matrix_rank(
    matrix: list[list[Fraction]], budget: _ExactBudget,
) -> int:
    """Exact rational forward Gaussian elimination, including bit checks."""
    nrows = len(matrix)
    ncols = len(matrix[0])
    rank = 0
    for col in range(ncols):
        pivot = next((row for row in range(rank, nrows)
                      if matrix[row][col] != 0), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        pivot_value = matrix[rank][col]
        for row in range(rank + 1, nrows):
            entry = matrix[row][col]
            if entry == 0:
                continue
            factor = budget.div(entry, pivot_value)
            matrix[row][col] = Fraction(0)
            for column in range(col + 1, ncols):
                matrix[row][column] = budget.sub(
                    matrix[row][column],
                    budget.mul(factor, matrix[rank][column]),
                )
        rank += 1
        if rank == nrows:
            break
    return rank


def _assignment_masks(variables: tuple[int, ...]) -> list[int]:
    return [
        sum((1 << variable) for j, variable in enumerate(variables)
            if assignment & (1 << j))
        for assignment in range(1 << len(variables))
    ]


def unfolding_rank(
    formula: CNFFormula, replacements: ReplacementSystem | None = None, *,
    at: Rational, left_variables: tuple[int, ...],
    limits: RankLimits = RankLimits(),
) -> UnfoldingRank:
    """Measure exact Q-rank of F_at(x_L,x_R) for an explicitly chosen cut.

    Enumerating 2**n cells is intrinsic to this *small-instance oracle*,
    not a proposed efficient counting algorithm. A bound from factor
    coefficient supports is recorded separately and is only an upper
    bound: cancellations can reduce the actual rank.
    """
    if not isinstance(formula, CNFFormula):
        raise TypeError("formula must be a CNFFormula")
    if not isinstance(limits, RankLimits):
        raise TypeError("limits must be RankLimits")
    center = _exact_fraction(at)  # rejects floats and booleans
    n = formula.nvars
    if n > limits.max_variables:
        raise CapacityError("ETH unfolding rank variable limit")
    cells = 1 << n
    if cells > limits.max_cells:
        raise CapacityError("ETH unfolding rank matrix cells limit")
    if (not isinstance(left_variables, tuple)
            or any(type(x) is not int or x < 0 or x >= n for x in left_variables)
            or len(set(left_variables)) != len(left_variables)):
        raise ValueError("left_variables must be unique declared zero-based indices")
    left = left_variables
    left_set = frozenset(left)
    right = tuple(i for i in range(n) if i not in left_set)
    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    replacements.validate(formula)

    budget = _ExactBudget(limits)
    budget.check(center)
    # Evaluate exact replacement coefficients once, with charged Horner
    # arithmetic; this includes the cost of preparing the matrix entries.
    prepared: list[tuple[tuple[Fraction, ...], ...]] = []
    boundary_left: set[int] = set()
    boundary_right: set[int] = set()
    for forms in replacements.clauses:
        rows: list[tuple[Fraction, ...]] = []
        support: set[int] = set()
        for form in forms:
            coeffs: list[Fraction] = []
            for polynomial in form.coefficients:
                value = Fraction(0)
                for coefficient in reversed(polynomial.coefficients):
                    value = budget.add(budget.mul(value, center), coefficient)
                coeffs.append(value)
                if value:
                    support.add(len(coeffs) - 1)
            rows.append(tuple(coeffs))
        prepared.append(tuple(rows))
        if support & left_set and support - left_set:
            boundary_left.update(support & left_set)
            boundary_right.update(support - left_set)

    left_masks = _assignment_masks(left)
    right_masks = _assignment_masks(right)
    matrix: list[list[Fraction]] = []
    total = Fraction(0)
    for a in left_masks:
        row: list[Fraction] = []
        for b in right_masks:
            assignment = a | b
            value = Fraction(1)
            for clause, prepared_occurrences in zip(formula.clauses, prepared):
                unsatisfied = Fraction(1)
                for literal, coefficients in zip(clause, prepared_occurrences):
                    linear = Fraction(0)
                    for variable, coefficient in enumerate(coefficients):
                        if assignment & (1 << variable):
                            linear = budget.add(linear, coefficient)
                    false_literal = (
                        budget.sub(Fraction(1), linear)
                        if literal > 0 else linear
                    )
                    unsatisfied = budget.mul(unsatisfied, false_literal)
                value = budget.mul(value, budget.sub(Fraction(1), unsatisfied))
            row.append(value)
            total = budget.add(total, value)
        matrix.append(row)

    exact_rank = _matrix_rank(matrix, budget)
    upper = 1 << min(len(boundary_left), len(boundary_right))
    if exact_rank > upper:
        raise ArithmeticError("unfolding rank exceeds a certified factor-cut bound")
    return UnfoldingRank(
        center=center,
        left_variables=left,
        right_variables=right,
        matrix_rows=len(left_masks),
        matrix_columns=len(right_masks),
        matrix_cells=cells,
        rank=exact_rank,
        boundary_rank_upper=upper,
        left_boundary_size=len(boundary_left),
        right_boundary_size=len(boundary_right),
        total_value=total,
        rational_operations=budget.operations,
        max_coefficient_bits=budget.max_bits,
    )


def rank_profile(
    formula: CNFFormula, replacements: ReplacementSystem | None = None, *,
    at: Rational, variable_order: Sequence[int],
    limits: RankLimits = RankLimits(),
) -> tuple[UnfoldingRank, ...]:
    """Full exact tensor-train rank profile for one specified ordering.

    Each cut is evaluated separately by the deliberately exponential
    reference. A different ordering can have radically smaller ranks.
    """
    order = tuple(variable_order)
    if (len(order) != formula.nvars
            or any(type(x) is not int for x in order)
            or set(order) != set(range(formula.nvars))):
        raise ValueError("variable_order must be a permutation of all variables")
    return tuple(
        unfolding_rank(
            formula, replacements, at=at, left_variables=order[:i], limits=limits,
        )
        for i in range(1, formula.nvars)
    )


def minimax_unfolding_order(
    formula: CNFFormula, replacements: ReplacementSystem | None = None, *,
    at: Rational, limits: RankLimits = RankLimits(), max_cuts: int = 64,
) -> MinimaxOrdering:
    """Exhaustively certify the smallest possible maximum TT bond rank.

    A cut rank depends on a subset of variables, not on the order inside
    either side. Enumerate all 2**n-2 proper nonempty subsets once, then
    apply subset minimax dynamic programming:

      best[S] = min_{v in S} max(best[S-v], rank(S)).

    The full-set rank is ignored because it is not a TT internal bond.
    This is exponential *diagnostic* work, never a production shortcut.
    """
    if type(max_cuts) is not int or max_cuts < 0:
        raise ValueError("max_cuts must be a nonnegative integer")
    n = formula.nvars
    if n > limits.max_variables:
        raise CapacityError("ETH unfolding rank variable limit")
    number_of_cuts = (1 << n) - 2 if n > 0 else 0
    if number_of_cuts > max_cuts:
        raise CapacityError("ETH unfolding rank cut search limit")
    full = (1 << n) - 1
    ranks: dict[int, int] = {}
    operations = 0
    max_bits = 0
    for subset in range(1, full):
        left = tuple(i for i in range(n) if subset & (1 << i))
        result = unfolding_rank(
            formula, replacements, at=at, left_variables=left, limits=limits,
        )
        ranks[subset] = result.rank
        operations += result.rational_operations
        max_bits = max(max_bits, result.max_coefficient_bits)

    # Sort candidates by (maximum bond rank, lexicographic order) for
    # deterministic, auditable tie-breaking.
    # A zero tensor has rank-zero unfolding at every internal cut.
    # Starting from 1 incorrectly promotes its optimum to 1.
    best: dict[int, tuple[int, tuple[int, ...]]] = {0: (0, ())}
    for subset in range(1, full + 1):
        possible: list[tuple[int, tuple[int, ...]]] = []
        for variable in range(n):
            bit = 1 << variable
            if not subset & bit:
                continue
            prior_max, prior_order = best[subset ^ bit]
            peak = max(prior_max, ranks.get(subset, 0))
            possible.append((peak, prior_order + (variable,)))
        best[subset] = min(possible)
    optimum, order = best[full]
    # For n <= 1 no internal TT bond exists; report the conventional
    # empty-profile value of one. For n >= 2, the exact zero-tensor
    # optimum is legitimately zero.
    if n <= 1:
        optimum = 1
    prefix = 0
    cut_ranks: list[int] = []
    for variable in order[:-1]:
        prefix |= 1 << variable
        cut_ranks.append(ranks[prefix])
    return MinimaxOrdering(
        variable_order=order, peak_rank=optimum, cut_ranks=tuple(cut_ranks),
        cuts_checked=number_of_cuts, charged_rational_operations=operations,
        max_coefficient_bits=max_bits,
    )
