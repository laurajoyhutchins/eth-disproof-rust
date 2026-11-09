"""Small-instance exact rational reference for the paper's H(T) identity.

This module does not implement measurement separation or interpolation. The
Boolean cube is explicitly enumerated, exclusively as a correctness oracle.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from non_exponential_sudoku.runtime.budget import CapacityError
from .cnf import CNFFormula
from .backends import (
    ArithmeticBackend, _NativePoly, _native_bits, check_arithmetic_backend,
    flint_taylor, require_flint,
)

Rational = int | Fraction


def _exact_fraction(value: object) -> Fraction:
    # Do not silently turn an already rounded binary float into a "rational".
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise TypeError('polynomial coefficients must be exact int or Fraction')
    return Fraction(value)


@dataclass(frozen=True, slots=True)
class Polynomial:
    """Canonical dense univariate polynomial over Q, low degree first."""

    coefficients: tuple[Fraction, ...]

    def __post_init__(self) -> None:
        values = tuple(_exact_fraction(value) for value in self.coefficients)
        while len(values) > 1 and values[-1] == 0:
            values = values[:-1]
        object.__setattr__(self, 'coefficients', values if values else (Fraction(0),))

    @classmethod
    def constant(cls, value: Rational) -> Polynomial:
        return cls((_exact_fraction(value),))

    @classmethod
    def variable(cls) -> Polynomial:
        return cls((Fraction(0), Fraction(1)))

    @property
    def degree(self) -> int:
        return len(self.coefficients) - 1

    @property
    def at_zero(self) -> Fraction:
        return self.coefficients[0]

    def __add__(self, other: Polynomial) -> Polynomial:
        n = max(len(self.coefficients), len(other.coefficients))
        return Polynomial(tuple(
            (self.coefficients[i] if i < len(self.coefficients) else Fraction(0)) +
            (other.coefficients[i] if i < len(other.coefficients) else Fraction(0))
            for i in range(n)))

    def __neg__(self) -> Polynomial:
        return Polynomial(tuple(-c for c in self.coefficients))

    def __sub__(self, other: Polynomial) -> Polynomial:
        return self + (-other)

    def __mul__(self, other: Polynomial) -> Polynomial:
        values = [Fraction(0)] * (len(self.coefficients) + len(other.coefficients) - 1)
        for i, a in enumerate(self.coefficients):
            for j, b in enumerate(other.coefficients):
                values[i + j] += a * b
        return Polynomial(tuple(values))

    def scale(self, value: Rational) -> Polynomial:
        factor = _exact_fraction(value)
        return Polynomial(tuple(c * factor for c in self.coefficients))

    def evaluate(self, at: Rational) -> Fraction:
        t = _exact_fraction(at)
        result = Fraction(0)
        for coefficient in reversed(self.coefficients):
            result = result * t + coefficient
        return result

    def taylor(self, center: Rational, order: int, *, backend: ArithmeticBackend = "python") -> Polynomial:
        """Exact first order+1 coefficients of H(center+z)."""
        if type(order) is not int or order < 0:
            raise ValueError('Taylor order must be nonnegative')
        check_arithmetic_backend(backend)
        if backend == 'flint':
            return Polynomial(flint_taylor(self.coefficients, _exact_fraction(center), order))
        z = Polynomial.variable()
        substitution = z + Polynomial.constant(center)
        result = Polynomial.constant(0)
        for coefficient in reversed(self.coefficients):
            result = (result * substitution + Polynomial.constant(coefficient)).truncate(order)
        return result

    def truncate(self, degree: int) -> Polynomial:
        if type(degree) is not int or degree < 0:
            raise ValueError('Truncation degree must be nonnegative')
        return Polynomial(self.coefficients[:degree + 1])


ZERO = Polynomial.constant(0)
ONE = Polynomial.constant(1)


@dataclass(frozen=True, slots=True)
class ReplacementForm:
    """P_{e,v}(T) dot x, with one rational polynomial per Boolean variable."""

    coefficients: tuple[Polynomial, ...]

    def evaluate_assignment(self, assignment: int) -> Polynomial:
        result = ZERO
        for index, coefficient in enumerate(self.coefficients):
            if assignment & (1 << index):
                result = result + coefficient
        return result


@dataclass(frozen=True, slots=True)
class ReplacementSystem:
    """One row of occurrence-specific linear forms per CNF clause."""

    clauses: tuple[tuple[ReplacementForm, ...], ...]

    @classmethod
    def identity(cls, formula: CNFFormula) -> ReplacementSystem:
        identities = tuple(
            ReplacementForm(tuple(ONE if i == j else ZERO for i in range(formula.nvars)))
            for j in range(formula.nvars)
        )
        return cls(tuple(tuple(identities[abs(lit) - 1] for lit in clause)
                         for clause in formula.clauses))

    def validate(self, formula: CNFFormula) -> None:
        if len(self.clauses) != len(formula.clauses):
            raise ValueError('replacement clause count mismatch')
        for clause, rows in zip(formula.clauses, self.clauses):
            if len(rows) != len(clause):
                raise ValueError('replacement occurrence count mismatch')
            for literal, form in zip(clause, rows):
                if len(form.coefficients) != formula.nvars:
                    raise ValueError('replacement must have nvars coefficients')
                if any(coeff.at_zero != (1 if index == abs(literal) - 1 else 0)
                       for index, coeff in enumerate(form.coefficients)):
                    raise ValueError('replacement must equal the original variable at T=0')


@dataclass(frozen=True, slots=True)
class ReferenceLimits:
    """Safe explicit caps for exponential research-only polynomial evaluation."""

    max_variables: int = 10
    max_assignments: int = 1 << 10
    max_degree: int = 256
    max_operations: int = 2_000_000
    max_coefficient_bits: int = 4096

    def __post_init__(self) -> None:
        for name in ('max_variables', 'max_assignments', 'max_degree', 'max_operations', 'max_coefficient_bits'):
            value = getattr(self, name)
            if type(value) is not int or value < (0 if name in ('max_variables', 'max_degree') else 1):
                raise ValueError(f'{name} must be a valid nonnegative/positive integer')


_PolyValue = Polynomial | _NativePoly


class _WorkBudget:
    """One cost model for independent Python and persistent native arithmetic.

    The FLINT branch converts a public Polynomial only on its first use. Its
    subsequent intermediate values never leave FLINT until final export.
    """

    def __init__(self, limits: ReferenceLimits, backend: ArithmeticBackend) -> None:
        self.limits = limits
        self.operations = 0
        self.flint = require_flint() if backend == 'flint' else None
        # Identity cache prevents repeated conversion per Boolean assignment;
        # a strong reference also prevents object-id reuse within this budget.
        self._inputs: dict[int, tuple[Polynomial, _NativePoly]] = {}

    def charge(self, cost: int) -> None:
        self.operations += cost
        if self.operations > self.limits.max_operations:
            raise CapacityError('ETH reference arithmetic operation limit')

    def _native(self, value: _PolyValue) -> _NativePoly:
        if isinstance(value, _NativePoly):
            return value
        if self.flint is None:
            raise TypeError('native polynomial requested with Python backend')
        cached = self._inputs.get(id(value))
        if cached is not None and cached[0] is value:
            return cached[1]
        result = _NativePoly.from_coefficients(value.coefficients, self.flint)
        self._inputs[id(value)] = (value, result)
        return result

    @staticmethod
    def _length(value: _PolyValue) -> int:
        return value.length if isinstance(value, _NativePoly) else len(value.coefficients)

    def check(self, result: _PolyValue) -> _PolyValue:
        if result.degree > self.limits.max_degree:
            raise CapacityError('ETH reference polynomial degree limit')
        bits = (_native_bits(result) if isinstance(result, _NativePoly)
                else (max(abs(c.numerator).bit_length(), c.denominator.bit_length())
                      for c in result.coefficients))
        if any(size > self.limits.max_coefficient_bits for size in bits):
            raise CapacityError('ETH reference coefficient bit limit')
        return result

    def add(self, left: _PolyValue, right: _PolyValue) -> _PolyValue:
        self.charge(max(self._length(left), self._length(right)))
        if self.flint is not None:
            result: _PolyValue = self._native(left) + self._native(right)
        else:
            if not isinstance(left, Polynomial) or not isinstance(right, Polynomial):
                raise TypeError('Python arithmetic requires reference polynomials')
            result = left + right
        return self.check(result)

    def multiply(self, left: _PolyValue, right: _PolyValue) -> _PolyValue:
        if left.degree + right.degree > self.limits.max_degree:
            raise CapacityError('ETH reference polynomial degree limit')
        self.charge(self._length(left) * self._length(right))
        if self.flint is not None:
            result: _PolyValue = self._native(left) * self._native(right)
        else:
            if not isinstance(left, Polynomial) or not isinstance(right, Polynomial):
                raise TypeError('Python arithmetic requires reference polynomials')
            result = left * right
        return self.check(result)

    def export(self, value: _PolyValue) -> Polynomial:
        return (Polynomial(value.export()) if isinstance(value, _NativePoly)
                else value)


def clause_satisfaction_polynomial(
    clause: tuple[int, ...], forms: tuple[ReplacementForm, ...], assignment: int,
) -> Polynomial:
    """Phi_e = 1 - product(1 - L_e,v) at a Boolean assignment."""
    if len(clause) != len(forms):
        raise ValueError('replacement occurrence count mismatch')
    unsatisfied = ONE
    for literal, form in zip(clause, forms):
        y = form.evaluate_assignment(assignment)
        unsatisfied = unsatisfied * (ONE - y if literal > 0 else y)
    return ONE - unsatisfied


def deformation_polynomial(
    formula: CNFFormula, replacements: ReplacementSystem | None = None,
    *, limits: ReferenceLimits = ReferenceLimits(), backend: ArithmeticBackend = "python",
) -> Polynomial:
    """Directly compute H(T) by explicit Boolean enumeration (oracle only).

    The checked P(0)=unit-vector invariant implies H(0)=#F. Every call
    checks it, and an invalid replacement fails rather than miscounting.
    """
    check_arithmetic_backend(backend)
    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    replacements.validate(formula)
    assignments = 1 << formula.nvars
    if formula.nvars > limits.max_variables or assignments > limits.max_assignments:
        raise CapacityError('ETH reference Boolean assignment limit')
    max_degree = sum(sum(max((coefficient.degree for coefficient in form.coefficients), default=0)
                         for form in rows) for rows in replacements.clauses)
    if max_degree > limits.max_degree:
        raise CapacityError('ETH reference polynomial degree limit')
    budget = _WorkBudget(limits, backend)
    for rows in replacements.clauses:
        for form in rows:
            for coefficient in form.coefficients:
                budget.check(coefficient)
    total: _PolyValue = ZERO
    for assignment in range(assignments):
        product: _PolyValue = ONE
        for clause, forms in zip(formula.clauses, replacements.clauses):
            unsatisfied: _PolyValue = ONE
            for literal, form in zip(clause, forms):
                linear: _PolyValue = ZERO
                for index, coefficient in enumerate(form.coefficients):
                    if assignment & (1 << index):
                        linear = budget.add(linear, coefficient)
                factor = budget.add(ONE, -linear) if literal > 0 else linear
                unsatisfied = budget.multiply(unsatisfied, factor)
            product = budget.multiply(product, budget.add(ONE, -unsatisfied))
        total = budget.add(total, product)
    return budget.export(total)
