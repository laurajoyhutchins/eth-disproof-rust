"""ETH-004: exact separated restricted Taylor sums and Boolean differences.

Implements the October 25 manuscript's restricted-sum identity at manually
certified measurement centers. There is no Boolean-cube fallback and no
construction of the paper's low-degree designs or parameter schedule.
All indices in E and U are zero-based Boolean variable indices.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal
from fractions import Fraction
from itertools import combinations, product
from math import comb

from non_exponential_sudoku.runtime.budget import CapacityError

from .backends import ArithmeticBackend, _coefficients, _q, check_arithmetic_backend, require_flint
from .cnf import CNFFormula
from .design import MeasurementCertificate, MeasurementDesign, certify_measurements
from .polynomial import Polynomial, Rational, ReplacementSystem, _exact_fraction


@dataclass(frozen=True, slots=True)
class Jet:
    """Canonical exact element of Q[z]/(z**(order+1)), low degree first."""

    coefficients: tuple[Fraction, ...]
    order: int

    def __post_init__(self) -> None:
        if type(self.order) is not int or self.order < 0:
            raise ValueError('jet order must be a nonnegative integer')
        if len(self.coefficients) > self.order + 1:
            raise ValueError('jet coefficients exceed truncation order')
        values = tuple(_exact_fraction(value) for value in self.coefficients)
        while len(values) > 1 and values[-1] == 0:
            values = values[:-1]
        object.__setattr__(self, 'coefficients', values if values else (Fraction(0),))

    @classmethod
    def constant(cls, value: Rational, order: int) -> Jet:
        return cls((_exact_fraction(value),), order)

    def full_coefficients(self) -> tuple[Fraction, ...]:
        return self.coefficients + (Fraction(0),) * (self.order + 1 - len(self.coefficients))

    def __add__(self, other: Jet) -> Jet:
        if self.order != other.order:
            raise ValueError('jet orders must match')
        left = self.full_coefficients()
        right = other.full_coefficients()
        return Jet(tuple(a + b for a, b in zip(left, right)), self.order)

    def __neg__(self) -> Jet:
        return Jet(tuple(-c for c in self.coefficients), self.order)

    def __sub__(self, other: Jet) -> Jet:
        return self + (-other)

    def __mul__(self, other: Jet) -> Jet:
        if self.order != other.order:
            raise ValueError('jet orders must match')
        result = [Fraction(0)] * (self.order + 1)
        for i, a in enumerate(self.coefficients):
            for j, b in enumerate(other.coefficients[:self.order - i + 1]):
                result[i + j] += a * b
        return Jet(tuple(result), self.order)


@dataclass(frozen=True, slots=True)
class TaylorLimits:
    """Explicit caps for proof-of-identity research, not performance claims."""

    max_variables: int | None = None
    max_taylor_order: int | None = None
    max_replacement_degree: int = 64
    max_occurrences: int = 2_000
    max_cached_corrections: int = 64
    max_taylor_pairs: int = 2_000
    max_measurement_tuples: int = 100_000
    max_group_assignments: int = 2_000_000
    max_jet_operations: int = 5_000_000
    max_coefficient_bits: int = 4096
    max_factor_entries: int = 100_000
    max_factor_total_entries: int = 200_000
    max_factor_work: int = 2_000_000

    def __post_init__(self) -> None:
        for field in self.__dataclass_fields__:
            value = getattr(self, field)
            if value is None and field in ('max_variables', 'max_taylor_order'):
                continue
            if type(value) is not int or value < (0 if field in (
                'max_variables', 'max_taylor_order', 'max_replacement_degree') else 1):
                raise ValueError(f'{field} must be a nonnegative/positive integer')


@dataclass(frozen=True, slots=True)
class TaylorStats:
    taylor_pairs: int
    measurement_tuples: int
    group_assignments_tried: int
    group_assignments_matching: int
    clause_evaluations: int
    jet_operations: int
    max_coefficient_bits: int
    factor_assignments_tested: int = 0
    factor_scope_peak: int = 0
    factor_entries_peak: int = 0
    factor_eliminations: int = 0
    factor_scope_basis: Literal['groups', 'variables'] = 'groups'


@dataclass(frozen=True, slots=True)
class TaylorResult:
    center: Fraction
    order: int
    coefficients: tuple[Fraction, ...]
    certificate: MeasurementCertificate
    stats: TaylorStats


@dataclass(frozen=True, slots=True)
class _FlintJet:
    """Internal exact Q[z]/z**(order+1), retaining the native polynomial.

    Only ``full_coefficients`` crosses the public Fraction boundary. FLINT
    values never escape into the independently executable Python reference.
    """

    poly: Any
    order: int

    def full_coefficients(self) -> tuple[Fraction, ...]:
        coefficients = _coefficients(self.poly)
        return coefficients + (Fraction(0),) * (self.order + 1 - len(coefficients))


_JetValue = Jet | _FlintJet


class _JetArithmetic:
    def __init__(self, limits: TaylorLimits, backend: ArithmeticBackend) -> None:
        self.limits = limits
        self.backend = backend
        self.operations = 0
        self.max_bits = 0
        self.flint = require_flint() if backend == 'flint' else None
        # Cached, *checked* constant polynomials. This bounds memory even when
        # the evaluator visits many distinct rational measurement values.
        self._constant_cache: dict[Fraction, _FlintJet] = {}

    def charge(self, amount: int) -> None:
        self.operations += amount
        if self.operations > self.limits.max_jet_operations:
            raise CapacityError('ETH Taylor jet operation limit')

    def constant(self, value: Rational, order: int) -> _JetValue:
        exact = _exact_fraction(value)
        if self.flint is None:
            return self.check(Jet.constant(exact, order))
        cached = self._constant_cache.get(exact)
        if cached is not None and cached.order == order:
            return cached
        if len(self._constant_cache) >= 256:
            self._constant_cache.clear()
        result = self.check(_FlintJet(self.flint.fmpq_poly([_q(exact, self.flint)]), order))
        assert isinstance(result, _FlintJet)
        self._constant_cache[exact] = result
        return result

    def variable(self, center: Fraction, order: int) -> _JetValue:
        if not order:
            return self.constant(center, order)
        if self.flint is None:
            return self.check(Jet((center, Fraction(1)), order))
        return self.check(_FlintJet(self.flint.fmpq_poly([_q(center, self.flint), 1]), order))

    def constant_term(self, value: _JetValue) -> Fraction:
        if isinstance(value, _FlintJet):
            return Fraction(int(value.poly[0].numerator), int(value.poly[0].denominator))
        return value.coefficients[0]

    def is_zero(self, value: _JetValue) -> bool:
        if isinstance(value, _FlintJet):
            return not bool(value.poly)
        return not any(value.coefficients)

    def _length(self, value: _JetValue) -> int:
        return max(1, len(value.poly)) if isinstance(value, _FlintJet) else len(value.coefficients)

    def check(self, value: _JetValue) -> _JetValue:
        if isinstance(value, _FlintJet):
            if len(value.poly) > value.order + 1:
                raise ValueError('FLINT jet exceeds truncation order')
            for coefficient in value.poly.coeffs():
                # Inspect fmpz bit lengths without constructing Python Fractions.
                bits = max(coefficient.numerator.bit_length(),
                           coefficient.denominator.bit_length())
                self.max_bits = max(self.max_bits, bits)
                if bits > self.limits.max_coefficient_bits:
                    raise CapacityError('ETH Taylor coefficient bit limit')
        else:
            for coefficient in value.coefficients:
                bits = max(coefficient.numerator.bit_length(), coefficient.denominator.bit_length())
                self.max_bits = max(self.max_bits, bits)
                if bits > self.limits.max_coefficient_bits:
                    raise CapacityError('ETH Taylor coefficient bit limit')
        return value

    def _binary(self, operation: str, left: _JetValue, right: _JetValue) -> _JetValue:
        if left.order != right.order:
            raise ValueError('jet orders must match')
        if self.flint is not None:
            if not isinstance(left, _FlintJet) or not isinstance(right, _FlintJet):
                raise TypeError('FLINT arithmetic requires native jet values')
            if operation == 'add':
                polynomial = left.poly + right.poly
            elif operation == 'sub':
                polynomial = left.poly - right.poly
            else:
                polynomial = left.poly * right.poly
            return self.check(_FlintJet(polynomial.truncate(left.order + 1), left.order))
        if not isinstance(left, Jet) or not isinstance(right, Jet):
            raise TypeError('reference arithmetic requires Python jet values')
        if operation == 'add':
            return self.check(left + right)
        if operation == 'sub':
            return self.check(left - right)
        return self.check(left * right)

    def add(self, left: _JetValue, right: _JetValue) -> _JetValue:
        self.charge(max(self._length(left), self._length(right)))
        return self._binary('add', left, right)

    def sub(self, left: _JetValue, right: _JetValue) -> _JetValue:
        self.charge(max(self._length(left), self._length(right)))
        return self._binary('sub', left, right)

    def mul(self, left: _JetValue, right: _JetValue) -> _JetValue:
        self.charge(sum(min(self._length(right), left.order - i + 1)
                        for i in range(self._length(left))))
        return self._binary('mul', left, right)


def _shift_polynomial(
    polynomial: Polynomial, center: Fraction, order: int, arithmetic: _JetArithmetic,
) -> _JetValue:
    """Horner shift with truncation after *every* multiplication."""
    if polynomial.degree > arithmetic.limits.max_replacement_degree:
        raise CapacityError('ETH Taylor replacement polynomial degree limit')
    variable = arithmetic.variable(center, order)
    value = arithmetic.constant(0, order)
    for coefficient in reversed(polynomial.coefficients):
        value = arithmetic.add(arithmetic.mul(value, variable),
                               arithmetic.constant(coefficient, order))
    return value


def _validate_indices(
    E: tuple[int, ...], U: tuple[int, ...], nvars: int,
) -> None:
    if (any(type(i) is not int or not 0 <= i < nvars for i in E + U)
            or tuple(sorted(set(E))) != E or tuple(sorted(set(U))) != U):
        raise ValueError('E and U must be sorted unique zero-based indices')
    if not set(U).issubset(E):
        raise ValueError('U must be a subset of E')


class _TaylorEvaluator:
    def __init__(
        self, formula: CNFFormula, replacements: ReplacementSystem,
        certificate: MeasurementCertificate, order: int, limits: TaylorLimits,
        expected_pairs: int, backend: ArithmeticBackend,
        summation: Literal['tuples', 'eliminate', 'fused'] = 'tuples',
    ) -> None:
        self.formula = formula
        self.certificate = certificate
        self.order = order
        self.limits = limits
        self.arithmetic = _JetArithmetic(limits, backend)
        if summation not in ('tuples', 'eliminate', 'fused'):
            raise ValueError('summation must be tuples, eliminate or fused')
        self.summation = summation
        self.factor_scope_basis: Literal['groups', 'variables'] = (
            'variables' if summation == 'fused' else 'groups')
        self.factor_assignments = 0
        self.factor_scope_peak = 0
        self.factor_entries_peak = 0
        self.factor_eliminations = 0
        if (type(order) is not int or order < 0 or
                (limits.max_taylor_order is not None and order > limits.max_taylor_order)):
            raise CapacityError('ETH Taylor order limit')
        if limits.max_variables is not None and formula.nvars > limits.max_variables:
            raise CapacityError('ETH Taylor variable limit')
        if expected_pairs > limits.max_taylor_pairs:
            raise CapacityError('ETH Taylor pair limit')
        design = certificate.design
        tuples_per_pair = (2 * design.D + 1) ** certificate.total_measurements
        assignments_per_pair = tuples_per_pair * sum(1 << len(g) for g in design.groups)
        if summation == 'tuples':
            if tuples_per_pair * expected_pairs > limits.max_measurement_tuples:
                raise CapacityError('ETH Taylor measurement tuple limit')
            if assignments_per_pair * expected_pairs > limits.max_group_assignments:
                raise CapacityError('ETH Taylor group assignment limit')
        self.tuples_per_pair = tuples_per_pair if summation == 'tuples' else 0
        self.pairs = 0
        self.tried = 0
        self.matching = 0
        self.clause_evaluations = 0
        self.offsets: list[int] = []
        offset = 0
        for rows in design.matrices:
            self.offsets.append(offset)
            offset += len(rows)
        self.clauses_by_group: list[list[int]] = [[] for _ in design.groups]
        for e, g in enumerate(design.clause_groups):
            self.clauses_by_group[g].append(e)
        self.zero = self.arithmetic.constant(0, order)
        self.one = self.arithmetic.constant(1, order)
        self.shifts: tuple[tuple[tuple[_JetValue, ...], ...], ...] = tuple(
            tuple(tuple(self._delta(p) for p in form.coefficients) for form in rows)
            for rows in replacements.clauses
        )
        # Cache U-specific corrections; none depend on a Boolean summation assignment.
        self._corrections: dict[tuple[int, ...], tuple[tuple[_JetValue, ...], ...]] = {}
        # Check certificate values, not just the shifted coefficients.
        for certified_rows in certificate.occurrences:
            for occ in certified_rows:
                for value in occ.local:
                    self.arithmetic.constant(value, order)
                for lambdas in occ.lambda_by_group:
                    for value in lambdas:
                        self.arithmetic.constant(value, order)

    def _delta(self, polynomial: Polynomial) -> _JetValue:
        shifted = _shift_polynomial(polynomial, self.certificate.center,
                                    self.order, self.arithmetic)
        return self.arithmetic.sub(
            shifted, self.arithmetic.constant(self.arithmetic.constant_term(shifted), self.order))

    def _get_corrections(self, U: tuple[int, ...]) -> tuple[tuple[_JetValue, ...], ...]:
        if U not in self._corrections:
            # A bounded cache avoids materializing 2**n large correction tables.
            if len(self._corrections) >= self.limits.max_cached_corrections:
                self._corrections.clear()
            result: list[tuple[_JetValue, ...]] = []
            for rows in self.shifts:
                corrections: list[_JetValue] = []
                for form in rows:
                    correction = self.zero
                    for index in U:
                        correction = self.arithmetic.add(correction, form[index])
                    corrections.append(correction)
                result.append(tuple(corrections))
            self._corrections[U] = tuple(result)
        return self._corrections[U]

    def restricted(self, E: tuple[int, ...], U: tuple[int, ...]) -> _JetValue:
        _validate_indices(E, U, self.formula.nvars)
        if len(E) > self.order:
            raise ValueError('restricted E size must not exceed Taylor order')
        self.pairs += 1
        if self.pairs > self.limits.max_taylor_pairs:
            raise CapacityError('ETH Taylor pair limit')
        corrections = self._get_corrections(U)
        if self.summation == 'eliminate':
            from .factorized_taylor import eliminate_restricted
            return eliminate_restricted(self, E, corrections)
        cert = self.certificate
        design = cert.design
        group_required = tuple(tuple(j for j, index in enumerate(group) if index in E)
                               for group in design.groups)
        total = self.zero
        for y in product(range(-design.D, design.D + 1), repeat=cert.total_measurements):
            group_product = self.one
            for g, (group, matrix) in enumerate(zip(design.groups, design.matrices)):
                wanted = y[self.offsets[g]:self.offsets[g] + len(matrix)]
                group_sum = self.zero
                for mask in range(1 << len(group)):
                    self.tried += 1
                    if any(not (mask & (1 << j)) for j in group_required[g]):
                        continue
                    bits = tuple((mask >> j) & 1 for j in range(len(group)))
                    if any(sum(coef * bit for coef, bit in zip(row, bits)) != value
                           for row, value in zip(matrix, wanted)):
                        continue
                    self.matching += 1
                    group_factor = self.one
                    for e in self.clauses_by_group[g]:
                        unsatisfied = self.one
                        for literal, occurrence, correction in zip(
                            self.formula.clauses[e], cert.occurrences[e], corrections[e],
                        ):
                            base = Fraction(0)
                            for coeff, bit in zip(occurrence.local, bits):
                                if bit:
                                    base += coeff
                            for h, lambdas in enumerate(occurrence.lambda_by_group):
                                for j, weight in enumerate(lambdas):
                                    base += weight * y[self.offsets[h] + j]
                            linear = self.arithmetic.add(self.arithmetic.constant(base, self.order), correction)
                            false_literal = (self.arithmetic.sub(self.one, linear)
                                             if literal > 0 else linear)
                            unsatisfied = self.arithmetic.mul(unsatisfied, false_literal)
                        group_factor = self.arithmetic.mul(
                            group_factor, self.arithmetic.sub(self.one, unsatisfied))
                        self.clause_evaluations += 1
                    group_sum = self.arithmetic.add(group_sum, group_factor)
                group_product = self.arithmetic.mul(group_product, group_sum)
                if self.arithmetic.is_zero(group_product):
                    break
            total = self.arithmetic.add(total, group_product)
        return total

    def stats(self) -> TaylorStats:
        return TaylorStats(
            taylor_pairs=self.pairs,
            measurement_tuples=self.pairs * self.tuples_per_pair,
            group_assignments_tried=self.tried,
            group_assignments_matching=self.matching,
            clause_evaluations=self.clause_evaluations,
            jet_operations=self.arithmetic.operations,
            max_coefficient_bits=self.arithmetic.max_bits,
            factor_assignments_tested=self.factor_assignments,
            factor_scope_peak=self.factor_scope_peak,
            factor_entries_peak=self.factor_entries_peak,
            factor_eliminations=self.factor_eliminations,
            factor_scope_basis=self.factor_scope_basis,
        )


def _make_evaluator(
    formula: CNFFormula, design: MeasurementDesign,
    replacements: ReplacementSystem | None, at: Rational,
    order: int, limits: TaylorLimits, pairs: int, backend: ArithmeticBackend,
    summation: Literal['tuples', 'eliminate', 'fused'] = 'tuples',
) -> _TaylorEvaluator:
    check_arithmetic_backend(backend)
    if (type(order) is not int or order < 0 or
                (limits.max_taylor_order is not None and order > limits.max_taylor_order)):
        raise CapacityError('ETH Taylor order limit')
    if limits.max_variables is not None and formula.nvars > limits.max_variables:
        raise CapacityError('ETH Taylor variable limit')
    if sum(len(clause) for clause in formula.clauses) > limits.max_occurrences:
        raise CapacityError('ETH Taylor clause occurrence limit')
    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    for rows in replacements.clauses:
        for form in rows:
            for polynomial in form.coefficients:
                if polynomial.degree > limits.max_replacement_degree:
                    raise CapacityError('ETH Taylor replacement polynomial degree limit')
                if any(max(coeff.numerator.bit_length(), coeff.denominator.bit_length()) >
                       limits.max_coefficient_bits for coeff in polynomial.coefficients):
                    raise CapacityError('ETH Taylor coefficient bit limit')
    center = _exact_fraction(at)
    if max(center.numerator.bit_length(), center.denominator.bit_length()) > limits.max_coefficient_bits:
        raise CapacityError('ETH Taylor center bit limit')
    certificate = certify_measurements(formula, replacements, design, at=center, backend=backend)
    return _TaylorEvaluator(formula, replacements, certificate, order, limits,
                            pairs, backend, summation)


def restricted_taylor_sum(
    formula: CNFFormula, design: MeasurementDesign,
    replacements: ReplacementSystem | None = None, *,
    at: Rational, E: tuple[int, ...], U: tuple[int, ...],
    order: int, limits: TaylorLimits = TaylorLimits(), backend: ArithmeticBackend = "python",
    summation: Literal['tuples', 'eliminate'] = 'tuples',
) -> TaylorResult:
    """Z_{t,E,U}(z), with x_i=1 for i in E and formal X=1_U.

    The only enumeration is over shared measurement tuples and group-local
    Boolean assignments. Invalid designs and exhausted budgets fail closed.
    """
    _validate_indices(E, U, formula.nvars)
    evaluator = _make_evaluator(
        formula, design, replacements, at, order, limits, 1, backend, summation)
    result = evaluator.restricted(E, U)
    return TaylorResult(evaluator.certificate.center, order, result.full_coefficients(),
                        evaluator.certificate, evaluator.stats())


def taylor_coefficients_separated(
    formula: CNFFormula, design: MeasurementDesign,
    replacements: ReplacementSystem | None = None, *,
    at: Rational, order: int, limits: TaylorLimits = TaylorLimits(),
    backend: ArithmeticBackend = "python",
    summation: Literal['tuples', 'eliminate', 'fused'] = 'tuples',
) -> TaylorResult:
    """Calculate [z^0..q] H(t+z) via the paper's Boolean differences.

    Sum over U subset E subset [n], |E|<=q, with alternating signs.
    The construction of valid measurement designs is *not* performed here.
    """
    if (type(order) is not int or order < 0 or
                (limits.max_taylor_order is not None and order > limits.max_taylor_order)):
        raise CapacityError('ETH Taylor order limit')
    n = formula.nvars
    if summation == 'fused':
        # The exact finite differences telescope before tensor contraction.
        # No E/U pairs are executed. The resulting factor width is measured
        # over the original Boolean variables, and can be exponential.
        from .fused_taylor import contract_fused_taylor
        prepared = (replacements if replacements is not None
                    else ReplacementSystem.identity(formula))
        evaluator = _make_evaluator(
            formula, design, prepared, at, order, limits, 0, backend, summation,
        )
        result = contract_fused_taylor(evaluator, prepared)
        return TaylorResult(
            evaluator.certificate.center, order, result.full_coefficients(),
            evaluator.certificate, evaluator.stats(),
        )
    pairs = sum(comb(n, j) * (1 << j) for j in range(min(order, n) + 1))
    evaluator = _make_evaluator(
        formula, design, replacements, at, order, limits, pairs, backend, summation)
    total = evaluator.zero
    for size in range(min(order, n) + 1):
        for E in combinations(range(n), size):
            for subset_size in range(size + 1):
                for U in combinations(E, subset_size):
                    contribution = evaluator.restricted(E, U)
                    total = (evaluator.arithmetic.add(total, contribution)
                             if (size - subset_size) % 2 == 0 else
                             evaluator.arithmetic.sub(total, contribution))
    return TaylorResult(evaluator.certificate.center, order, total.full_coefficients(),
                        evaluator.certificate, evaluator.stats())
