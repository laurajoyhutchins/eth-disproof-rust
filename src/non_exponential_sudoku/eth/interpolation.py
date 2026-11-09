"""ETH-004: exact rational confluent Hermite interpolation and manual path.

Interpolate from truncated H(t+z) at distinct nonzero rational centers,
using an incremental polynomial CRT with exact division by a nonzero unit.
The manual path demands certified measurements at every chosen center and
never substitutes an exhaustive #SAT oracle for a missing design.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import comb
from fractions import Fraction
from typing import Any, Protocol, Sequence, TypeVar

from non_exponential_sudoku.runtime.budget import CapacityError

from .backends import (
    ArithmeticBackend, _NativePoly, _native_bits, _q, check_arithmetic_backend,
    require_flint,
)
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
class HermiteOriginResult:
    """Only the origin value of the unique polynomial of degree < conditions."""

    value: Fraction
    stats: HermiteStats


@dataclass(frozen=True, slots=True)
class OriginManualCountResult:
    """Count-only certified Taylor/Hermite path, without an explicit polynomial."""

    count: int
    taylor_data: tuple[TaylorResult, ...]
    hermite_stats: HermiteStats


@dataclass(frozen=True, slots=True)
class ManualCountResult:
    """Exact count from supplied designs, never a general-purpose ETH counter."""

    count: int
    polynomial: Polynomial
    taylor_data: tuple[TaylorResult, ...]
    hermite_stats: HermiteStats


_P = TypeVar('_P')
_J = TypeVar('_J')


class _HermiteArithmetic(Protocol[_P, _J]):
    """The mathematical reconstruction uses one algorithm, two exact rings."""

    operations: int
    max_bits: int

    def check_input(self, value: Fraction) -> None: ...
    def constant(self, value: Any) -> _P: ...
    def variable(self, center: Fraction) -> _P: ...
    def add(self, left: _P, right: _P) -> _P: ...
    def mul(self, left: _P, right: _P) -> _P: ...
    def shift(self, poly: _P, center: Fraction, order: int) -> _J: ...
    def datum_jet(self, datum: HermiteDatum) -> _J: ...
    def subtract(self, left: _J, right: _J) -> _J: ...
    def quotient(self, numerator: _J, denominator: _J, order: int) -> tuple[Any, ...]: ...
    def matches(self, jet: _J, datum: HermiteDatum) -> bool: ...
    def degree(self, poly: _P) -> int: ...
    def export(self, poly: _P) -> Polynomial: ...


class _PythonHermiteArithmetic:
    """Independently executable Fraction/Polynomial correctness oracle."""

    def __init__(self, limits: HermiteLimits) -> None:
        self.limits = limits
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

    def check_input(self, value: Fraction) -> None:
        self.check_fraction(value)

    def poly(self, poly: Polynomial) -> Polynomial:
        if poly.degree > self.limits.max_conditions:
            raise CapacityError('ETH Hermite intermediate degree limit')
        for coefficient in poly.coefficients:
            self.check_fraction(coefficient)
        return poly

    def constant(self, value: Fraction | int) -> Polynomial:
        return Polynomial.constant(value)

    def variable(self, center: Fraction) -> Polynomial:
        return self.poly(Polynomial((-center, Fraction(1))))

    def add(self, left: Polynomial, right: Polynomial) -> Polynomial:
        self.charge(max(len(left.coefficients), len(right.coefficients)))
        return self.poly(left + right)

    def mul(self, left: Polynomial, right: Polynomial) -> Polynomial:
        self.charge(len(left.coefficients) * len(right.coefficients))
        return self.poly(left * right)

    def shift(self, poly: Polynomial, center: Fraction, order: int) -> Jet:
        base = Jet((center, Fraction(1)), order) if order else Jet.constant(center, order)
        value = Jet.constant(0, order)
        for coefficient in reversed(poly.coefficients):
            self.charge(len(value.coefficients) * len(base.coefficients) + order + 1)
            value = value * base + Jet.constant(coefficient, order)
            for c in value.coefficients:
                self.check_fraction(c)
        return value

    def datum_jet(self, datum: HermiteDatum) -> Jet:
        return Jet(datum.coefficients, len(datum.coefficients) - 1)

    def subtract(self, left: Jet, right: Jet) -> Jet:
        return left - right

    def quotient(self, numerator: Jet, denominator: Jet, order: int) -> tuple[Fraction, ...]:
        if numerator.order != denominator.order or numerator.order != order:
            raise ValueError('Hermite jet orders mismatch')
        b = denominator.full_coefficients()
        a = numerator.full_coefficients()
        if b[0] == 0:
            raise ValueError('Hermite centers must be distinct')
        coeffs: list[Fraction] = []
        for j in range(order + 1):
            self.charge(2 * j + 1)
            residual = self.check_fraction(a[j] - sum(
                (b[i] * coeffs[j - i] for i in range(1, j + 1)), Fraction(0)))
            coeffs.append(self.check_fraction(residual / b[0]))
        return tuple(coeffs)

    def matches(self, jet: Jet, datum: HermiteDatum) -> bool:
        return jet.full_coefficients() == datum.coefficients

    def degree(self, poly: Polynomial) -> int:
        return poly.degree

    def export(self, poly: Polynomial) -> Polynomial:
        return poly


class _FlintHermiteArithmetic:
    """Retain native Q[T] and Q[z] through all Hermite CRT updates.

    Native numerators/denominators are inspected at every reference check
    point. There are no intermediate Fraction allocations or text conversions.
    """

    def __init__(self, limits: HermiteLimits) -> None:
        self.limits = limits
        self.flint = require_flint()
        self.operations = 0
        self.max_bits = 0

    def charge(self, amount: int) -> None:
        self.operations += amount
        if self.operations > self.limits.max_operations:
            raise CapacityError('ETH Hermite rational operation limit')

    def check_scalar(self, value: Any) -> Any:
        bits = max(value.numerator.bit_length(), value.denominator.bit_length())
        self.max_bits = max(self.max_bits, bits)
        if bits > self.limits.max_coefficient_bits:
            raise CapacityError('ETH Hermite coefficient bit limit')
        return value

    def check_input(self, value: Fraction) -> None:
        self.check_scalar(_q(value, self.flint))

    def poly(self, poly: _NativePoly) -> _NativePoly:
        if poly.degree > self.limits.max_conditions:
            raise CapacityError('ETH Hermite intermediate degree limit')
        for bits in _native_bits(poly):
            self.max_bits = max(self.max_bits, bits)
            if bits > self.limits.max_coefficient_bits:
                raise CapacityError('ETH Hermite coefficient bit limit')
        return poly

    def constant(self, value: Any) -> _NativePoly:
        if isinstance(value, Fraction):
            scalar = _q(value, self.flint)
        else:
            scalar = value
        return _NativePoly(self.flint.fmpq_poly([scalar]))

    def variable(self, center: Fraction) -> _NativePoly:
        return self.poly(_NativePoly(self.flint.fmpq_poly([_q(-center, self.flint), 1])))

    def add(self, left: _NativePoly, right: _NativePoly) -> _NativePoly:
        self.charge(max(left.length, right.length))
        return self.poly(left + right)

    def mul(self, left: _NativePoly, right: _NativePoly) -> _NativePoly:
        self.charge(left.length * right.length)
        return self.poly(left * right)

    def shift(self, poly: _NativePoly, center: Fraction, order: int) -> _NativePoly:
        base = self.flint.fmpq_poly([_q(center, self.flint), 1] if order else
                                     [_q(center, self.flint)])
        value = self.flint.fmpq_poly([])
        # The reference zero polynomial has one coefficient; account for
        # its Horner step even though FLINT encodes zero with length zero.
        coefficients = poly.value.coeffs() or [self.flint.fmpq(0, 1)]
        for coefficient in reversed(coefficients):
            self.charge(max(1, len(value)) * max(1, len(base)) + order + 1)
            # For the mock protocol, truncated multiplication is emulated.
            product = (value.mul_low(base, order + 1) if hasattr(value, 'mul_low')
                       else (value * base).truncate(order + 1))
            value = (product + self.flint.fmpq_poly([coefficient])).truncate(order + 1)
            for bits in _native_bits(_NativePoly(value)):
                self.max_bits = max(self.max_bits, bits)
                if bits > self.limits.max_coefficient_bits:
                    raise CapacityError('ETH Hermite coefficient bit limit')
        return _NativePoly(value)

    def datum_jet(self, datum: HermiteDatum) -> _NativePoly:
        return _NativePoly.from_coefficients(datum.coefficients, self.flint)

    def subtract(self, left: _NativePoly, right: _NativePoly) -> _NativePoly:
        # The independent reference does not charge the residual subtraction.
        return left - right

    def quotient(self, numerator: _NativePoly, denominator: _NativePoly,
                 order: int) -> tuple[Any, ...]:
        """Native truncated division using an explicit, local jet precision."""
        b0 = denominator.value[0]
        if b0 == 0:
            raise ValueError('Hermite centers must be distinct')
        zero = self.flint.fmpq(0, 1)
        coeffs: list[Any] = []
        for j in range(order + 1):
            self.charge(2 * j + 1)
            residual = self.check_scalar(numerator.value[j] - sum(
                (denominator.value[i] * coeffs[j - i] for i in range(1, j + 1)), zero))
            coeffs.append(self.check_scalar(residual / b0))
        return tuple(coeffs)

    def matches(self, jet: _NativePoly, datum: HermiteDatum) -> bool:
        return all(jet.value[i] == _q(value, self.flint)
                   for i, value in enumerate(datum.coefficients))

    def degree(self, poly: _NativePoly) -> int:
        return poly.degree

    def export(self, poly: _NativePoly) -> Polynomial:
        return Polynomial(poly.export())


def _interpolate_with_arithmetic(
    data: Sequence[HermiteDatum], degree_bound: int,
    budget: _HermiteArithmetic[_P, _J],
) -> HermiteResult:
    """Incremental polynomial CRT; backend-neutral exact mathematical steps."""
    solution = budget.constant(0)
    modulus = budget.constant(1)
    for datum in data:
        order = len(datum.coefficients) - 1
        for coefficient in datum.coefficients:
            budget.check_input(coefficient)
        residual = budget.subtract(budget.datum_jet(datum), budget.shift(solution, datum.center, order))
        denominator = budget.shift(modulus, datum.center, order)
        correction = budget.quotient(residual, denominator, order)
        variable = budget.variable(datum.center)
        shifted = budget.constant(0)
        for coefficient in reversed(correction):
            shifted = budget.add(budget.mul(shifted, variable), budget.constant(coefficient))
        solution = budget.add(solution, budget.mul(modulus, shifted))
        for _ in correction:
            modulus = budget.mul(modulus, variable)
    if budget.degree(solution) > degree_bound:
        raise ValueError('Hermite data inconsistent with supplied degree bound')
    for datum in data:
        if not budget.matches(budget.shift(solution, datum.center, len(datum.coefficients) - 1), datum):
            raise ArithmeticError('Hermite reconstruction verification failed')
    return HermiteResult(budget.export(solution), HermiteStats(
        centers=len(data), total_conditions=sum(len(d.coefficients) for d in data),
        rational_operations=budget.operations, max_coefficient_bits=budget.max_bits,
    ))


def interpolate_hermite(
    data: Sequence[HermiteDatum], *, degree_bound: int,
    limits: HermiteLimits = HermiteLimits(), backend: ArithmeticBackend = 'python',
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
    if backend == 'flint':
        return _interpolate_with_arithmetic(data, degree_bound, _FlintHermiteArithmetic(limits))
    return _interpolate_with_arithmetic(data, degree_bound, _PythonHermiteArithmetic(limits))


def interpolate_origin_hermite(
    data: Sequence[HermiteDatum], *, limits: HermiteLimits = HermiteLimits(),
) -> HermiteOriginResult:
    """Evaluate the Hermite interpolant at zero without constructing it.

    For each center c_i and order J_i, let M_i(T) be the product of
    (T-c_j)**J_j over OTHER centers.  Its local inverse exists because
    centers are distinct.  The Hermite CRT identity gives:

        P(0) = sum_i M_i(0) *
               [(P(c_i+z) / M_i(c_i+z)) mod z**J_i]_(z=-c_i).

    As with any Hermite interpolant, this reconstructs the unique polynomial
    of degree below the TOTAL number of conditions.  It does not independently
    certify a tighter claimed degree bound or inconsistent redundant data.
    Use it with independently certified polynomial Taylor data.
    """
    if not data:
        raise ValueError('Hermite origin needs at least one center')
    if any(not isinstance(datum, HermiteDatum) for datum in data):
        raise TypeError('origin recovery requires HermiteDatum inputs')
    centers = tuple(datum.center for datum in data)
    if len(set(centers)) != len(centers):
        raise ValueError('Hermite centers must be distinct')
    conditions = sum(len(datum.coefficients) for datum in data)
    if conditions > limits.max_conditions:
        raise CapacityError('ETH Hermite condition limit')
    if conditions - 1 > limits.max_degree:
        raise CapacityError('ETH Hermite degree limit')

    budget = _PythonHermiteArithmetic(limits)
    for datum in data:
        for coefficient in datum.coefficients:
            budget.check_input(coefficient)

    def truncated_product(
        left: Sequence[Fraction], right: Sequence[Fraction], order: int,
    ) -> tuple[Fraction, ...]:
        coefficients = [Fraction(0)] * order
        for i, a in enumerate(left):
            if i >= order:
                break
            if a == 0:
                continue
            for j, b in enumerate(right):
                if i + j >= order:
                    break
                if b == 0:
                    continue
                budget.charge(1)
                coefficients[i + j] = budget.check_fraction(
                    coefficients[i + j] + a * b)
        return tuple(coefficients)

    origin = Fraction(0)
    for index, datum in enumerate(data):
        order = len(datum.coefficients)
        local_modulus: tuple[Fraction, ...] = (Fraction(1),)
        modulus_at_zero = Fraction(1)
        for j, other in enumerate(data):
            if index == j:
                continue
            multiplicity = len(other.coefficients)
            gap = datum.center - other.center
            modulus_at_zero = budget.check_fraction(
                modulus_at_zero * (-other.center) ** multiplicity)
            factor = tuple(budget.check_fraction(
                Fraction(comb(multiplicity, k)) * gap ** (multiplicity - k))
                for k in range(min(multiplicity, order - 1) + 1))
            local_modulus = truncated_product(local_modulus, factor, order)

        if local_modulus[0] == 0:
            raise ArithmeticError('Hermite local modulus is not invertible')
        inverse = [budget.check_fraction(1 / local_modulus[0])]
        for k in range(1, order):
            budget.charge(k + 1)
            residual = sum(
                (local_modulus[j] * inverse[k - j] for j in range(1, k + 1)),
                Fraction(0),
            )
            inverse.append(budget.check_fraction(-residual / local_modulus[0]))
        quotient = truncated_product(datum.coefficients, inverse, order)
        value = Fraction(0)
        for coefficient in reversed(quotient):
            budget.charge(1)
            value = budget.check_fraction(value * -datum.center + coefficient)
        budget.charge(1)
        origin = budget.check_fraction(origin + modulus_at_zero * value)

    return HermiteOriginResult(origin, HermiteStats(
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


def count_origin_from_manual_designs(
    formula: CNFFormula,
    centers: Sequence[tuple[Rational, MeasurementDesign]],
    replacements: ReplacementSystem | None = None,
    *,
    order: int,
    taylor_limits: TaylorLimits = TaylorLimits(),
    hermite_limits: HermiteLimits = HermiteLimits(),
    backend: ArithmeticBackend = "python",
) -> OriginManualCountResult:
    """Exact count-only readout from separately certified Taylor jets.

    The certified replacement construction bounds the degree of the true
    deformation polynomial.  There is no brute-force counting fallback.
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
    if (any(center == 0 for center in centers_normalized)
            or len(set(centers_normalized)) != len(centers)):
        raise ValueError('nonzero distinct interpolation centers required')
    if degree > hermite_limits.max_degree:
        raise CapacityError('ETH Hermite degree limit')
    collected: list[TaylorResult] = []
    for center, (_, design) in zip(centers_normalized, centers):
        collected.append(taylor_coefficients_separated(
            formula, design, replacements, at=center, order=order,
            limits=taylor_limits, backend=backend,
        ))
    result = interpolate_origin_hermite(
        tuple(HermiteDatum(entry.center, entry.coefficients) for entry in collected),
        limits=hermite_limits,
    )
    value = result.value
    if value.denominator != 1 or not 0 <= value <= (1 << formula.nvars):
        raise ArithmeticError('reconstructed count violates exact CNF count invariants')
    return OriginManualCountResult(int(value), tuple(collected), result.stats)
