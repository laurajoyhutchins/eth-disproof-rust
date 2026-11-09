"""ETH-003: bounded exact rational summation over shared measurements.

Computes H(t) by group-local Boolean sums, *not* a full Boolean-cube
fallback. The measurement design must be supplied and certified at t.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product

from non_exponential_sudoku.runtime.budget import CapacityError

from .cnf import CNFFormula
from .design import MeasurementCertificate, MeasurementDesign, certify_measurements
from .polynomial import Rational, ReplacementSystem


@dataclass(frozen=True, slots=True)
class SeparatedLimits:
    max_variables: int | None = None
    max_measurement_tuples: int = 100_000
    max_group_assignments: int = 2_000_000
    max_operations: int = 2_000_000
    max_coefficient_bits: int = 4096

    def __post_init__(self) -> None:
        for name in ('max_variables', 'max_measurement_tuples', 'max_group_assignments',
                     'max_operations', 'max_coefficient_bits'):
            value = getattr(self, name)
            if value is None and name == 'max_variables':
                continue
            if type(value) is not int or value < (0 if name == 'max_variables' else 1):
                raise ValueError(f'{name} must be a nonnegative/positive integer')


@dataclass(frozen=True, slots=True)
class SeparatedStats:
    measurement_tuples: int
    group_assignments_tried: int
    group_assignments_matching: int
    clause_evaluations: int
    rational_operations: int
    max_coefficient_bits: int


@dataclass(frozen=True, slots=True)
class SeparatedResult:
    value: Fraction
    certificate: MeasurementCertificate
    stats: SeparatedStats


class _Arithmetic:
    def __init__(self, limits: SeparatedLimits) -> None:
        self.limits = limits
        self.operations = 0
        self.max_bits = 0

    def check(self, value: Fraction) -> Fraction:
        size = max(value.numerator.bit_length(), value.denominator.bit_length())
        self.max_bits = max(self.max_bits, size)
        if size > self.limits.max_coefficient_bits:
            raise CapacityError('ETH separated coefficient bit limit')
        return value

    def add(self, a: Fraction, b: Fraction) -> Fraction:
        self.charge()
        return self.check(a + b)

    def mul(self, a: Fraction, b: Fraction) -> Fraction:
        self.charge()
        return self.check(a * b)

    def charge(self) -> None:
        self.operations += 1
        if self.operations > self.limits.max_operations:
            raise CapacityError('ETH separated rational operation limit')


def evaluate_separated(
    formula: CNFFormula,
    design: MeasurementDesign,
    replacements: ReplacementSystem | None = None,
    *,
    at: Rational = 1,
    limits: SeparatedLimits = SeparatedLimits(),
) -> SeparatedResult:
    """Evaluate H(at) using the manuscript's separated-sum identity.

    Never enumerates assignments to all n variables. Checks exact rational
    row-space witnesses before doing group sums. Up-front limits bound the
    number of measurement tuples and Boolean group assignments to be tried.
    """
    if limits.max_variables is not None and formula.nvars > limits.max_variables:
        raise CapacityError('ETH separated variable limit')
    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    certificate = certify_measurements(formula, replacements, design, at=at)
    count = (2 * design.D + 1) ** certificate.total_measurements
    group_total = sum(1 << len(group) for group in design.groups)
    if count > limits.max_measurement_tuples:
        raise CapacityError('ETH separated measurement tuple limit')
    if count * group_total > limits.max_group_assignments:
        raise CapacityError('ETH separated group assignment limit')

    arithmetic = _Arithmetic(limits)
    for rows in certificate.occurrences:
        for occurrence in rows:
            for value in occurrence.local:
                arithmetic.check(value)
            for lambdas in occurrence.lambda_by_group:
                for value in lambdas:
                    arithmetic.check(value)

    zero = Fraction(0)
    one = Fraction(1)
    offsets: list[int] = []
    offset = 0
    for matrix in design.matrices:
        offsets.append(offset)
        offset += len(matrix)
    clauses_by_group: list[list[int]] = [[] for _ in design.groups]
    for e, g in enumerate(design.clause_groups):
        clauses_by_group[g].append(e)

    tried = 0
    matching = 0
    clause_evaluations = 0
    total = zero
    for y in product(range(-design.D, design.D + 1), repeat=certificate.total_measurements):
        group_product = one
        for g, (group, matrix) in enumerate(zip(design.groups, design.matrices)):
            wanted = y[offsets[g]:offsets[g] + len(matrix)]
            group_sum = zero
            for mask in range(1 << len(group)):
                tried += 1
                bits = tuple((mask >> j) & 1 for j in range(len(group)))
                if any(sum(coef * bit for coef, bit in zip(row, bits)) != val
                       for row, val in zip(matrix, wanted)):
                    continue
                matching += 1
                factor = one
                for e in clauses_by_group[g]:
                    unsatisfied = one
                    for literal, occurrence in zip(formula.clauses[e], certificate.occurrences[e]):
                        linear = zero
                        for coeff, bit in zip(occurrence.local, bits):
                            if bit:
                                linear = arithmetic.add(linear, coeff)
                        for h, lambdas in enumerate(occurrence.lambda_by_group):
                            for j, weight in enumerate(lambdas):
                                if weight:
                                    term = arithmetic.mul(weight, Fraction(y[offsets[h] + j]))
                                    linear = arithmetic.add(linear, term)
                        false_literal = arithmetic.add(one, -linear) if literal > 0 else linear
                        unsatisfied = arithmetic.mul(unsatisfied, false_literal)
                    factor = arithmetic.mul(factor, arithmetic.add(one, -unsatisfied))
                    clause_evaluations += 1
                group_sum = arithmetic.add(group_sum, factor)
            group_product = arithmetic.mul(group_product, group_sum)
            if not group_product:
                break
        total = arithmetic.add(total, group_product)
    return SeparatedResult(
        value=total,
        certificate=certificate,
        stats=SeparatedStats(
            measurement_tuples=count,
            group_assignments_tried=tried,
            group_assignments_matching=matching,
            clause_evaluations=clause_evaluations,
            rational_operations=arithmetic.operations,
            max_coefficient_bits=arithmetic.max_bits,
        ),
    )
