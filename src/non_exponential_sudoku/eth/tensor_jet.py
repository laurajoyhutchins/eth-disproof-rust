"""Exact higher-order ETH tensor contraction in Q[z]/(z**(J+1)).

The tensor automaton is the order-zero construction with truncated
polynomial coefficients. A matrix over this ring cannot be reduced by
ordinary rational Gaussian elimination: z is a nonzero nonunit, and
nonzero jets may have zero constant coefficient.

Instead, column factorization repeatedly selects the entry of least
z-adic valuation, divides only by its unit part, subtracts an exact
rank-one matrix, and checks the remainder in the truncated ring.
Every result is an identity modulo z**(J+1), including nilpotents.
No precision-dropping or approximate-rank threshold is permitted.

This is a direct symbolic deformation evaluator, not the paper's
Boolean-difference Taylor algorithm. It certifies measurement
separation at the chosen center, but computes the varying coefficients
from the original replacement polynomials. The cost still depends
exponentially on local group mask size and potentially tensor bonds.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import TypeAlias

from non_exponential_sudoku.runtime.budget import CapacityError

from .cnf import CNFFormula
from .design import MeasurementCertificate, MeasurementDesign, certify_measurements
from .polynomial import Polynomial, Rational, ReplacementForm, ReplacementSystem, _exact_fraction
from .taylor import Jet
from .tensor_train import TensorLimits, TensorStats, _Budget
from .interpolation import (
    HermiteDatum, HermiteLimits, HermiteStats, _degree_upper_bound,
    interpolate_origin_hermite,
)

_JMatrix: TypeAlias = tuple[tuple[Jet, ...], ...]
_JCore: TypeAlias = tuple[_JMatrix, ...]
_JTrain: TypeAlias = tuple[_JCore, ...]


@dataclass(frozen=True, slots=True)
class TensorTaylorResult:
    """Exact coefficients of H(center+z) through order, with provenance."""

    center: Fraction
    order: int
    coefficients: tuple[Fraction, ...]
    certificate: MeasurementCertificate
    stats: TensorStats


class _JetBudget(_Budget):
    def __init__(self, order: int, limits: TensorLimits) -> None:
        super().__init__(limits)
        if type(order) is not int or order < 0 or order > limits.max_taylor_order:
            raise CapacityError('ETH tensor Taylor order limit')
        self.order = order
        self.zero = Jet.constant(0, order)
        self.one = Jet.constant(1, order)

    def check_jet(self, value: Jet) -> Jet:
        if value.order != self.order:
            raise ValueError('tensor jets must share the same truncation order')
        for coefficient in value.coefficients:
            self.check(coefficient)
        return value

    def constant(self, value: Rational) -> Jet:
        return self.check_jet(Jet.constant(value, self.order))

    def add_jet(self, left: Jet, right: Jet) -> Jet:
        self.operation(max(len(left.coefficients), len(right.coefficients)))
        return self.check_jet(left + right)

    def sub_jet(self, left: Jet, right: Jet) -> Jet:
        self.operation(max(len(left.coefficients), len(right.coefficients)))
        return self.check_jet(left - right)

    def mul_jet(self, left: Jet, right: Jet) -> Jet:
        self.operation(sum(min(len(right.coefficients), self.order - i + 1)
                           for i in range(len(left.coefficients))))
        return self.check_jet(left * right)

    def shift(self, polynomial: Polynomial, center: Fraction) -> Jet:
        """Exact truncated Horner evaluation at center+z."""
        if polynomial.degree > self.limits.max_replacement_degree:
            raise CapacityError('ETH tensor replacement polynomial degree limit')
        variable = (
            self.constant(center) if self.order == 0
            else self.check_jet(Jet((center, Fraction(1)), self.order))
        )
        result = self.zero
        for coefficient in reversed(polynomial.coefficients):
            result = self.add_jet(self.mul_jet(result, variable),
                                  self.constant(coefficient))
        return result

    def quotient(self, numerator: Jet, divisor: Jet) -> Jet:
        """Solve divisor*q=numerator in the truncated ring.

        Only called when v(divisor) is the smallest nonzero valuation
        of the residual matrix, hence v(numerator)>=v(divisor).
        We divide the shifted series by the UNIT part of the divisor.
        The result need not be unique due to nilpotents, but is exact.
        """
        a, b = numerator.full_coefficients(), divisor.full_coefficients()
        valuation = next((i for i, v in enumerate(b) if v), None)
        if valuation is None:
            raise ZeroDivisionError('zero tensor jet pivot')
        if any(a[:valuation]):
            raise ArithmeticError('nondivisible tensor jet pivot')
        unit = b[valuation]
        quotient: list[Fraction] = []
        for k in range(self.order + 1 - valuation):
            numerator_coefficient = a[k + valuation]
            for i in range(1, k + 1):
                numerator_coefficient = self.sub(
                    numerator_coefficient,
                    self.mul(b[i + valuation], quotient[k - i]),
                )
            quotient.append(self.div(numerator_coefficient, unit))
        result = self.check_jet(Jet(tuple(quotient), self.order))
        if self.mul_jet(divisor, result) != numerator:
            raise ArithmeticError('inexact tensor jet quotient')
        return result

    def core(self, domain: int, left: int, right: int,
             *, before: bool) -> None:
        entries = domain * left * right * (self.order + 1)
        if entries > self.limits.max_jet_coefficient_entries:
            raise CapacityError('ETH tensor jet coefficient entry limit')
        super().core(domain, left, right, before=before)


def _jet_column_factor(
    matrix: list[list[Jet]], budget: _JetBudget,
) -> tuple[list[list[Jet]], list[list[Jet]]]:
    """Exact A=U*V using valuation-minimal pivots, even with zero divisors.

    Repeatedly subtract residual_column * residual_pivot_row/pivot.
    All residual entries have valuation at least that of the pivot,
    making every quotient exact. The pivot row AND column vanish after
    subtraction. This bounds the number of factors by min(m,n), but
    does not claim a field-style rank theorem or optimal module width.
    """
    if not matrix or not matrix[0]:
        raise ValueError('empty tensor jet factor matrix')
    nrows, ncols = len(matrix), len(matrix[0])
    if any(len(row) != ncols for row in matrix):
        raise ValueError('inconsistent tensor jet factor matrix width')
    if nrows * ncols * (budget.order + 1) > budget.limits.max_jet_coefficient_entries:
        raise CapacityError('ETH tensor jet factor matrix entry limit')
    remaining = [[budget.check_jet(value) for value in row] for row in matrix]
    left_columns: list[list[Jet]] = []
    right_rows: list[list[Jet]] = []
    while True:
        candidate: tuple[int, int, int] | None = None
        for i, row in enumerate(remaining):
            for j, value in enumerate(row):
                valuation = next((k for k, coeff in enumerate(value.coefficients)
                                  if coeff), None)
                if valuation is not None and (
                    candidate is None or valuation < candidate[0]
                ):
                    candidate = (valuation, i, j)
        if candidate is None:
            break
        _, pivot_row, pivot_column = candidate
        pivot = remaining[pivot_row][pivot_column]
        column = [remaining[i][pivot_column] for i in range(nrows)]
        coordinates = [
            budget.quotient(remaining[pivot_row][j], pivot)
            for j in range(ncols)
        ]
        for i in range(nrows):
            for j in range(ncols):
                remaining[i][j] = budget.sub_jet(
                    remaining[i][j], budget.mul_jet(column[i], coordinates[j]))
        if any(any(value.coefficients) for value in remaining[pivot_row]) or any(
            any(remaining[i][pivot_column].coefficients)
            for i in range(nrows)
        ):
            raise ArithmeticError('tensor jet elimination failed to clear pivot')
        left_columns.append(column)
        right_rows.append(coordinates)
        if len(left_columns) > min(nrows, ncols):
            raise ArithmeticError('tensor jet factorization did not terminate')
    left = [
        [column[i] for column in left_columns] for i in range(nrows)
    ]
    return left, right_rows


def _dimensions(core: _JCore) -> tuple[int, int, int]:
    return len(core), len(core[0]), len(core[0][0])


def _bonds(train: _JTrain) -> tuple[int, ...]:
    return tuple(_dimensions(core)[2] for core in train[:-1])


def _ones(domains: tuple[int, ...], budget: _JetBudget) -> _JTrain:
    return tuple(tuple(((budget.one,),) for _ in range(domain))
                 for domain in domains)


def _zeros(domains: tuple[int, ...], budget: _JetBudget) -> _JTrain:
    return tuple(
        tuple(((budget.zero if g == 0 else budget.one,),)
              for _ in range(domain))
        for g, domain in enumerate(domains)
    )


def _dot(a: list[Jet], b: list[Jet], budget: _JetBudget) -> Jet:
    if len(a) != len(b):
        raise ArithmeticError('tensor jet dot-product dimension mismatch')
    value = budget.zero
    for x, y in zip(a, b):
        value = budget.add_jet(value, budget.mul_jet(x, y))
    return value


def _compress(train: _JTrain, domains: tuple[int, ...],
              budget: _JetBudget) -> _JTrain:
    """Two exact chain-ring factor sweeps, never constant-term RREF."""
    if len(train) < 2:
        return train
    cores: list[list[list[list[Jet]]]] = [
        [[list(row) for row in matrix] for matrix in core] for core in train
    ]
    for g in range(len(cores) - 1):
        domain, left, right = (len(cores[g]), len(cores[g][0]),
                               len(cores[g][0][0]))
        flat = [
            [cores[g][x][l][j] for j in range(right)]
            for l in range(left) for x in range(domain)
        ]
        independent, coefficients = _jet_column_factor(flat, budget)
        rank = len(coefficients)
        if rank == 0:
            return _zeros(domains, budget)
        budget.core(domain, left, rank, before=False)
        cores[g] = [
            [[independent[l * domain + x][k] for k in range(rank)]
             for l in range(left)]
            for x in range(domain)
        ]
        next_domain, next_left, next_right = (
            len(cores[g + 1]), len(cores[g + 1][0]),
            len(cores[g + 1][0][0]),
        )
        if next_left != right:
            raise ArithmeticError('tensor jet bond mismatch in left sweep')
        budget.core(next_domain, rank, next_right, before=False)
        cores[g + 1] = [
            [[_dot(coefficients[k],
                   [cores[g + 1][x][j][z] for j in range(right)], budget)
              for z in range(next_right)]
             for k in range(rank)]
            for x in range(next_domain)
        ]

    for g in range(len(cores) - 1, 0, -1):
        domain, left, right = (len(cores[g]), len(cores[g][0]),
                               len(cores[g][0][0]))
        transposed = [
            [cores[g][x][k][z] for k in range(left)]
            for x in range(domain) for z in range(right)
        ]
        independent, coefficients = _jet_column_factor(transposed, budget)
        rank = len(coefficients)
        if rank == 0:
            return _zeros(domains, budget)
        budget.core(domain, rank, right, before=False)
        cores[g] = [
            [[independent[x * right + z][k] for z in range(right)]
             for k in range(rank)]
            for x in range(domain)
        ]
        previous_domain, previous_left, previous_right = (
            len(cores[g - 1]), len(cores[g - 1][0]),
            len(cores[g - 1][0][0]),
        )
        if previous_right != left:
            raise ArithmeticError('tensor jet bond mismatch in right sweep')
        budget.core(previous_domain, previous_left, rank, before=False)
        cores[g - 1] = [
            [[_dot(cores[g - 1][x][k], coefficients[z], budget)
              for z in range(rank)]
             for k in range(previous_left)]
            for x in range(previous_domain)
        ]
    return tuple(
        tuple(tuple(tuple(row) for row in matrix) for matrix in core)
        for core in cores
    )


def _hadamard(
    left: _JTrain, right: _JTrain, domains: tuple[int, ...],
    budget: _JetBudget,
) -> _JTrain:
    result: list[_JCore] = []
    for g, (a, b) in enumerate(zip(left, right)):
        domain, la, ra = _dimensions(a)
        other_domain, lb, rb = _dimensions(b)
        if domain != other_domain or domain != domains[g]:
            raise ArithmeticError('tensor jet group domain mismatch')
        budget.core(domain, la * lb, ra * rb, before=True)
        core = tuple(
            tuple(
                tuple(
                    budget.mul_jet(a[x][i][j], b[x][k][z])
                    for j in range(ra) for z in range(rb)
                )
                for i in range(la) for k in range(lb)
            )
            for x in range(domain)
        )
        result.append(core)
    return tuple(result)


def _clause_train(
    clause: tuple[int, ...], forms: tuple[ReplacementForm, ...],
    owner: int, design: MeasurementDesign, domains: tuple[int, ...],
    center: Fraction, budget: _JetBudget,
) -> _JTrain:
    """Exact subset-state automaton for 1 - product of signed false jets."""
    if not clause:
        return _zeros(domains, budget)
    if len(forms) != len(clause):
        raise ArithmeticError('replacement occurrence count mismatch')
    width = len(clause)
    states = 1 << width
    constant_state, full = states, states - 1
    shifts = tuple(
        tuple(budget.shift(polynomial, center) for polynomial in form.coefficients)
        for form in forms
    )
    result: list[_JCore] = []
    for g, (group, domain) in enumerate(zip(design.groups, domains)):
        left = 1 if g == 0 else states + 1
        right = 1 if g == len(domains) - 1 else states + 1
        budget.core(domain, left, right, before=True)
        matrices: list[_JMatrix] = []
        for mask in range(domain):
            terms: list[Jet] = []
            for literal, shifted in zip(clause, shifts):
                linear = budget.zero
                for local_index, variable in enumerate(group):
                    if mask & (1 << local_index):
                        linear = budget.add_jet(linear, shifted[variable])
                false_term = (
                    budget.sub_jet(budget.one if g == owner else budget.zero, linear)
                    if literal > 0 else linear
                )
                terms.append(false_term)

            def transition(source: int, target: int) -> Jet:
                if source == constant_state or target == constant_state:
                    return budget.one if source == target == constant_state else budget.zero
                if source & target != source:
                    return budget.zero
                output = budget.one
                for literal_index in range(width):
                    if (target ^ source) & (1 << literal_index):
                        output = budget.mul_jet(output, terms[literal_index])
                return output

            matrix: list[tuple[Jet, ...]] = []
            for left_index in range(left):
                source_states = (
                    ((0, -1), (constant_state, 1)) if g == 0
                    else ((left_index, 1),)
                )
                row: list[Jet] = []
                for right_index in range(right):
                    targets = (
                        ((full, 1), (constant_state, 1))
                        if g == len(domains) - 1 else ((right_index, 1),)
                    )
                    value = budget.zero
                    for source, sign in source_states:
                        for target, coefficient in targets:
                            value = budget.add_jet(
                                value,
                                budget.mul_jet(
                                    budget.constant(sign * coefficient),
                                    transition(source, target),
                                ),
                            )
                    row.append(value)
                matrix.append(tuple(row))
            matrices.append(tuple(matrix))
        result.append(tuple(matrices))
    return tuple(result)


def _sum_all(train: _JTrain, budget: _JetBudget) -> Jet:
    vector = [budget.one]
    for core in train:
        _, left, right = _dimensions(core)
        if len(vector) != left:
            raise ArithmeticError('tensor jet summation bond mismatch')
        output = [budget.zero for _ in range(right)]
        for matrix in core:
            for i in range(left):
                for j in range(right):
                    output[j] = budget.add_jet(
                        output[j], budget.mul_jet(vector[i], matrix[i][j]))
        vector = output
    if len(vector) != 1:
        raise ArithmeticError('tensor jet summation did not terminate')
    return vector[0]


def contract_certified_taylor(
    formula: CNFFormula,
    design: MeasurementDesign,
    replacements: ReplacementSystem | None = None,
    *, at: Rational, order: int,
    limits: TensorLimits = TensorLimits(),
) -> TensorTaylorResult:
    """Exact H(at+z) coefficients through order, with bounded TT contraction.

    The chosen design is certified at the center, but derivatives are
    computed by directly shifting each ORIGINAL replacement polynomial.
    This does not require measuring its derivative directions and
    makes no claim about the paper's bounded-difference algorithm.
    """
    budget = _JetBudget(order, limits)
    groups = design.groups
    if len(groups) > limits.max_groups:
        raise CapacityError('ETH tensor group count limit')
    if len(formula.clauses) > limits.max_clauses:
        raise CapacityError('ETH tensor clause count limit')
    if sum(map(len, design.matrices)) > limits.max_measurement_rows:
        raise CapacityError('ETH tensor measurement row count limit')
    if any(len(group) >= limits.max_group_masks.bit_length()
           for group in groups):
        raise CapacityError('ETH tensor local group-mask limit')
    domains = tuple(1 << len(group) for group in groups)
    if any(domain > limits.max_group_masks for domain in domains):
        raise CapacityError('ETH tensor local group-mask limit')
    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    if any(poly.degree > limits.max_replacement_degree
           for clause in replacements.clauses for form in clause
           for poly in form.coefficients):
        raise CapacityError('ETH tensor replacement polynomial degree limit')
    center = _exact_fraction(at)
    budget.constant(center)
    certificate = certify_measurements(formula, replacements, design, at=center)
    state = _ones(domains, budget)
    history: list[tuple[int, ...]] = []
    for clause, forms, owner in zip(
        formula.clauses, replacements.clauses, design.clause_groups,
    ):
        local = _clause_train(
            clause, forms, owner, design, domains, center, budget)
        local = _compress(local, domains, budget)
        state = _hadamard(state, local, domains, budget)
        state = _compress(state, domains, budget)
        history.append(_bonds(state))
    final = _sum_all(state, budget)
    return TensorTaylorResult(
        center=certificate.center,
        order=order,
        coefficients=final.full_coefficients(),
        certificate=certificate,
        stats=TensorStats(
            clause_count=len(formula.clauses),
            local_masks=sum(domains),
            maximum_clause_width=max(map(len, formula.clauses), default=0),
            theoretical_clause_bond_bound=(
                (1 << max(map(len, formula.clauses), default=0)) + 1
            ),
            peak_bond_before_compression=budget.peak_bond_before,
            peak_bond_after_compression=budget.peak_bond_after,
            peak_core_entries=budget.peak_entries,
            rational_operations=budget.operations,
            maximum_coefficient_bits=budget.max_bits,
            final_bonds=_bonds(state),
            clause_bond_history=tuple(history),
        ),
    )



@dataclass(frozen=True, slots=True)
class TensorOriginCountResult:
    """Count-only Hermite reconstruction from exact certified tensor jets."""

    count: int
    center_results: tuple[TensorTaylorResult, ...]
    hermite_stats: HermiteStats


def count_origin_from_tensor_designs(
    formula: CNFFormula,
    centers: tuple[tuple[Rational, MeasurementDesign], ...],
    replacements: ReplacementSystem | None = None,
    *,
    order: int,
    tensor_limits: TensorLimits = TensorLimits(),
    hermite_limits: HermiteLimits = HermiteLimits(),
) -> TensorOriginCountResult:
    """Exact H(0) using tensor Taylor data plus independent Hermite CRT.

    Every center has its own certificate. No Boolean-cube count fallback,
    numerical approximation, or unproven degree bound is allowed.
    This is a research alternative to Boolean-difference evaluation.
    """
    if type(order) is not int or order < 0 or order > tensor_limits.max_taylor_order:
        raise CapacityError('ETH tensor Taylor order limit')
    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    replacements.validate(formula)
    if not centers:
        raise ValueError('at least one certified tensor center is required')
    normalized = tuple(_exact_fraction(center) for center, _ in centers)
    if any(center == 0 for center in normalized):
        raise ValueError('nonzero Hermite centers required')
    if len(set(normalized)) != len(normalized):
        raise ValueError('distinct Hermite centers required')
    degree = _degree_upper_bound(replacements)
    conditions = len(centers) * (order + 1)
    if conditions <= degree:
        raise ValueError('insufficient Hermite conditions for degree bound')
    if conditions > hermite_limits.max_conditions:
        raise CapacityError('ETH Hermite condition limit')
    if degree > hermite_limits.max_degree:
        raise CapacityError('ETH Hermite degree limit')

    results: list[TensorTaylorResult] = []
    for center, (_, design) in zip(normalized, centers):
        results.append(contract_certified_taylor(
            formula, design, replacements, at=center, order=order,
            limits=tensor_limits,
        ))
    interpolation = interpolate_origin_hermite(
        tuple(HermiteDatum(x.center, x.coefficients) for x in results),
        degree_bound=degree,
        limits=hermite_limits,
    )
    value = interpolation.value
    if value.denominator != 1 or not 0 <= value <= (1 << formula.nvars):
        raise ArithmeticError('tensor Hermite count violates exact CNF invariants')
    return TensorOriginCountResult(
        int(value), tuple(results), interpolation.stats,
    )
