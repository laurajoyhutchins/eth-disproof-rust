"""ETH-004: exact rational confluent Hermite interpolation and manual path.

Interpolate from truncated H(t+z) at distinct nonzero rational centers,
using an incremental polynomial CRT with exact division by a nonzero unit.
The manual path demands certified measurements at every chosen center and
never substitutes an exhaustive #SAT oracle for a missing design.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from non_exponential_sudoku.runtime.budget import CapacityError

from .backends import ArithmeticBackend, check_arithmetic_backend, flint_polynomial_op
from .cnf import CNFFormula
from .design import MeasurementDesign
from .polynomial import ONE, ZERO, Polynomial, Rational, ReplacementSystem, _exact_fraction
from .taylor import Jet, TaylorLimits, TaylorResult, taylor_coefficients_separated


@dataclass(frozen=True, slots=True)
class HermiteDatum:
    """Taylor coefficients H(center+z) from z**0 through z**(J-1)."""

    center: Fraction
    coefficients: tuple[Fraction, ...]

    def __post_init__(self) -> None:
        center = _exact_fraction(self.center)
        values = tuple(_exact_fraction(value) for value in self.coefficients)
        if center == 0:
            raise ValueError('the paper path uses nonzero Hermite centers')
        if not values:
            raise ValueError('Hermite datum needs at least one coefficient')
        object.__setattr__(self, 'center', center)
        object.__setattr__(self, 'coefficients', values)


@dataclass(frozen=True, slots=True)
class HermiteLimits:
    max_degree: int = 256
    max_conditions: int = 512
    max_operations: int = 5_000_000
    max_coefficient_bits: int = 4096

    def __post_init__(self) -> None:
        for field in self.__dataclass_fields__:
            value = getattr(self, field)
            if type(value) is not int or value < (0 if field == 'max_degree' else 1):
                raise ValueError(f'{field} must be a nonnegative/positive integer')


@dataclass(frozen=True, slots=True)
class HermiteStats:
    centers: int
    total_conditions: int
    rational_operations: int
    max_coefficient_bits: int


@dataclass(frozen=True, slots=True)
class HermiteResult:
    polynomial: Polynomial
    stats: HermiteStats


@dataclass(frozen=True, slots=True)
class ManualCountResult:
    """Exact count from supplied designs, never a general-purpose ETH counter."""

    count: int
    polynomial: Polynomial
    taylor_data: tuple[TaylorResult, ...]
    hermite_stats: HermiteStats


class _Budget:
    def __init__(self, limits: HermiteLimits, backend: ArithmeticBackend) -> None:
        self.limits = limits
        self.backend = backend
        self.operations = 0
        self.max_bits = 0

    def charge(self, amount: int) -> None:
        self.operations += amount
        if self.operations > self.limits.max_operations:
            raise CapacityError('ETH Hermite rational operation limit')

    def check_fraction(self, value: Fraction) -> Fraction:
        bits = max(value.numerator.bit_length(), value.denominator.bit_length())
        self.max_bits = max(self.max_bits, bits)
        if bits > self.limits.max_coefficient_bits:
            raise CapacityError('ETH Hermite coefficient bit limit')
        return value

    def poly(self, polynomial: Polynomial) -> Polynomial:
        if polynomial.degree > self.limits.max_conditions:
            raise CapacityError('ETH Hermite intermediate degree limit')
        for coefficient in polynomial.coefficients:
            self.check_fraction(coefficient)
        return polynomial

    def add(self, left: Polynomial, right: Polynomial) -> Polynomial:
        self.charge(max(len(left.coefficients), len(right.coefficients)))
        result = (Polynomial(flint_polynomial_op('add', left.coefficients, right.coefficients))
                  if self.backend == 'flint' else left + right)
        return self.poly(result)

    def mul(self, left: Polynomial, right: Polynomial) -> Polynomial:
        self.charge(len(left.coefficients) * len(right.coefficients))
        result = (Polynomial(flint_polynomial_op('mul', left.coefficients, right.coefficients))
                  if self.backend == 'flint' else left * right)
        return self.poly(result)

    def shift(self, polynomial: Polynomial, center: Fraction, order: int) -> Jet:
        """Horner shift directly into Q[z]/(z**(order+1))."""
        base = Jet((center, Fraction(1)), order) if order else Jet.constant(center, order)
        value = Jet.constant(0, order)
        for coefficient in reversed(polynomial.coefficients):
            self.charge((len(value.coefficients) * len(base.coefficients)) + order + 1)
            value = (Jet(flint_polynomial_op('mul', value.coefficients, base.coefficients,
                                             max_length=order + 1), order)
                     if self.backend == 'flint' else value * base)
            value = (Jet(flint_polynomial_op('add', value.coefficients, (coefficient,),
                                           max_length=order + 1), order)
                     if self.backend == 'flint' else value + Jet.constant(coefficient, order))
            for v in value.coefficients:
                self.check_fraction(v)
        return value

    def solve_jet_quotient(self, numerator: Jet, denominator: Jet) -> tuple[Fraction, ...]:
        """Solve B(z)C(z)=A(z) mod z**J, B(0) != 0."""
        if numerator.order != denominator.order:
            raise ValueError('Hermite jet orders mismatch')
        b = denominator.full_coefficients()
        a = numerator.full_coefficients()
        if b[0] == 0:
            raise ValueError('Hermite centers must be distinct')
        coeffs: list[Fraction] = []
        for j in range(numerator.order + 1):
            self.charge(2 * j + 1)
            residual = self.check_fraction(a[j] - sum(
                (b[i] * coeffs[j - i] for i in range(1, j + 1)), Fraction(0)))
            coeffs.append(self.check_fraction(residual / b[0]))
        return tuple(coeffs)


def interpolate_hermite(
    data: Sequence[HermiteDatum], *, degree_bound: int,
    limits: HermiteLimits = HermiteLimits(), backend: ArithmeticBackend = "python",
) -> HermiteResult:
    """Recover a unique rational polynomial from nonzero-center Taylor jets.

    Require sum(J_t)>degree_bound and distinct centers; return an explicit
    refusal for inconsistent data or insufficient constraints. Accepts
    different Taylor orders at different centers.
    """
    check_arithmetic_backend(backend)
    if type(degree_bound) is not int or degree_bound < 0:
        raise ValueError('degree_bound must be a nonnegative integer')
    if degree_bound > limits.max_degree:
        raise CapacityError('ETH Hermite degree limit')
    if not data:
        raise ValueError('Hermite interpolation needs at least one center')
    if any(not isinstance(datum, HermiteDatum) for datum in data):
        raise TypeError('interpolation requires HermiteDatum inputs')
    centers = tuple(datum.center for datum in data)
    if len(set(centers)) != len(centers):
        raise ValueError('Hermite centers must be distinct')
    conditions = sum(len(datum.coefficients) for datum in data)
    if conditions <= degree_bound:
        raise ValueError('insufficient Hermite conditions for the degree bound')
    if conditions > limits.max_conditions:
        raise CapacityError('ETH Hermite condition limit')
    budget = _Budget(limits, backend)
    solution = ZERO
    modulus = ONE
    for datum in data:
        order = len(datum.coefficients) - 1
        for coefficient in datum.coefficients:
            budget.check_fraction(coefficient)
        residual = Jet(datum.coefficients, order) - budget.shift(solution, datum.center, order)
        denominator = budget.shift(modulus, datum.center, order)
        correction = budget.solve_jet_quotient(residual, denominator)
        variable = budget.poly(Polynomial((-datum.center, Fraction(1))))
        shifted = ZERO
        for coefficient in reversed(correction):
            shifted = budget.add(budget.mul(shifted, variable), Polynomial.constant(coefficient))
        solution = budget.add(solution, budget.mul(modulus, shifted))
        for _ in correction:
            modulus = budget.mul(modulus, variable)
    if solution.degree > degree_bound:
        raise ValueError('Hermite data inconsistent with supplied degree bound')
    for datum in data:
        check = budget.shift(solution, datum.center, len(datum.coefficients) - 1)
        if check.full_coefficients() != datum.coefficients:
            raise ArithmeticError('Hermite reconstruction verification failed')
    return HermiteResult(solution, HermiteStats(
        centers=len(data), total_conditions=conditions,
        rational_operations=budget.operations, max_coefficient_bits=budget.max_bits,
    ))


def _degree_upper_bound(replacements: ReplacementSystem) -> int:
    return sum(sum(max((coefficient.degree for coefficient in form.coefficients), default=0)
                   for form in rows) for rows in replacements.clauses)


def count_from_manual_designs(
    formula: CNFFormula,
    centers: Sequence[tuple[Rational, MeasurementDesign]],
    replacements: ReplacementSystem | None = None,
    *, order: int,
    taylor_limits: TaylorLimits = TaylorLimits(),
    hermite_limits: HermiteLimits = HermiteLimits(),
    backend: ArithmeticBackend = "python",
) -> ManualCountResult:
    """ETH-004 end-to-end reference: certified designs -> Taylor -> #F.

    Every center needs its own valid measurement certificate. This path
    never constructs designs, enumerates the joint Boolean cube, or calls
    the brute-force reference algorithm. Its cost can remain exponential.
    """
    check_arithmetic_backend(backend)
    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    replacements.validate(formula)
    degree = _degree_upper_bound(replacements)
    if not centers:
        raise ValueError('at least one manually certified center is required')
    if type(order) is not int or order < 0:
        raise ValueError('Taylor order must be nonnegative')
    if len(centers) * (order + 1) <= degree:
        raise ValueError('insufficient Hermite conditions for degree bound')
    centers_normalized = [_exact_fraction(center) for center, _ in centers]
    if any(center == 0 for center in centers_normalized) or len(set(centers_normalized)) != len(centers):
        raise ValueError('nonzero distinct interpolation centers required')
    collected: list[TaylorResult] = []
    for center, (_, design) in zip(centers_normalized, centers):
        collected.append(taylor_coefficients_separated(
            formula, design, replacements, at=center, order=order, limits=taylor_limits, backend=backend))
    interpolation = interpolate_hermite(
        tuple(HermiteDatum(result.center, result.coefficients) for result in collected),
        degree_bound=degree, limits=hermite_limits, backend=backend,
    )
    value = interpolation.polynomial.at_zero
    if value.denominator != 1 or not 0 <= value <= (1 << formula.nvars):
        raise ArithmeticError('reconstructed count violates exact CNF count invariants')
    return ManualCountResult(int(value), interpolation.polynomial, tuple(collected),
                             interpolation.stats)
