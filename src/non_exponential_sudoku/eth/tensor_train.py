"""Exact rational tensor-train contraction for certified ETH value readouts.

This is an ORDER-ZERO experiment. It contracts H(center), not its
derivatives. Every signed literal is a sum of per-group affine functions;
the product of w such sums has an exact subset-automaton tensor train
with internal dimension at most 2**w+1, independent of the number of
participating groups. Product of clauses can nevertheless generate
exponentially large bonds. Exact rational rank sweeps and explicit
resource bounds expose rather than conceal that possibility.

No full Boolean cube, global measurement-tuple table, or clause
interaction table is allocated. Local group-mask domains still have
size 2**|group|; this is not a worst-case subexponential algorithm.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import TypeAlias

from non_exponential_sudoku.runtime.budget import CapacityError

from .cnf import CNFFormula
from .design import MeasurementCertificate, MeasurementDesign, certify_measurements
from .polynomial import Rational, ReplacementSystem

_Matrix: TypeAlias = tuple[tuple[Fraction, ...], ...]
_Core: TypeAlias = tuple[_Matrix, ...]
_Train: TypeAlias = tuple[_Core, ...]


@dataclass(frozen=True, slots=True)
class TensorLimits:
    max_groups: int = 12
    max_group_masks: int = 128
    max_clauses: int = 64
    max_measurement_rows: int = 512
    max_bond: int = 256
    max_core_entries: int = 100_000
    max_rational_operations: int = 4_000_000
    max_coefficient_bits: int = 4096

    def __post_init__(self) -> None:
        for name in self.__dataclass_fields__:
            value = getattr(self, name)
            if type(value) is not int or value < 1:
                raise ValueError(f'{name} must be a positive integer')


@dataclass(frozen=True, slots=True)
class TensorStats:
    clause_count: int
    local_masks: int
    maximum_clause_width: int
    theoretical_clause_bond_bound: int
    peak_bond_before_compression: int
    peak_bond_after_compression: int
    peak_core_entries: int
    rational_operations: int
    maximum_coefficient_bits: int
    final_bonds: tuple[int, ...]
    clause_bond_history: tuple[tuple[int, ...], ...]


@dataclass(frozen=True, slots=True)
class TensorContractionResult:
    center: Fraction
    value: Fraction
    certificate: MeasurementCertificate
    stats: TensorStats


class _Budget:
    def __init__(self, limits: TensorLimits) -> None:
        self.limits = limits
        self.operations = 0
        self.max_bits = 0
        self.peak_bond_before = 1
        self.peak_bond_after = 1
        self.peak_entries = 0

    def check(self, value: Fraction) -> Fraction:
        self.max_bits = max(self.max_bits, value.numerator.bit_length(),
                            value.denominator.bit_length())
        if self.max_bits > self.limits.max_coefficient_bits:
            raise CapacityError('ETH tensor rational coefficient bit limit')
        return value

    def operation(self, count: int = 1) -> None:
        self.operations += count
        if self.operations > self.limits.max_rational_operations:
            raise CapacityError('ETH tensor rational operation limit')

    def add(self, a: Fraction, b: Fraction) -> Fraction:
        self.operation()
        return self.check(a + b)

    def sub(self, a: Fraction, b: Fraction) -> Fraction:
        self.operation()
        return self.check(a - b)

    def mul(self, a: Fraction, b: Fraction) -> Fraction:
        self.operation()
        return self.check(a * b)

    def div(self, a: Fraction, b: Fraction) -> Fraction:
        self.operation()
        return self.check(a / b)

    def core(self, domain: int, left: int, right: int,
             *, before: bool) -> None:
        if left > self.limits.max_bond or right > self.limits.max_bond:
            raise CapacityError('ETH tensor bond dimension limit')
        entries = domain * left * right
        if entries > self.limits.max_core_entries:
            raise CapacityError('ETH tensor core entry limit')
        self.peak_entries = max(self.peak_entries, entries)
        if before:
            self.peak_bond_before = max(self.peak_bond_before, left, right)
        else:
            self.peak_bond_after = max(self.peak_bond_after, left, right)


def _dimensions(core: _Core) -> tuple[int, int, int]:
    return len(core), len(core[0]), len(core[0][0])


def _bonds(train: _Train) -> tuple[int, ...]:
    return tuple(_dimensions(core)[2] for core in train[:-1])


def _ones(domains: tuple[int, ...]) -> _Train:
    return tuple(
        tuple(((Fraction(1),),) for _ in range(domain))
        for domain in domains
    )


def _zeros(domains: tuple[int, ...]) -> _Train:
    return tuple(
        tuple(((Fraction(int(g != 0)),),) for _ in range(domain))
        for g, domain in enumerate(domains)
    )


def _dot(a: list[Fraction], b: list[Fraction], budget: _Budget) -> Fraction:
    if len(a) != len(b):
        raise ArithmeticError('tensor dot-product dimension mismatch')
    value = Fraction(0)
    for x, y in zip(a, b):
        value = budget.add(value, budget.mul(x, y))
    return value


def _column_factor(
    matrix: list[list[Fraction]], budget: _Budget,
) -> tuple[list[list[Fraction]], list[list[Fraction]]]:
    """Exact A=U*V, U independent original columns, V RREF coordinates.

    The pivot columns in Gauss-Jordan elimination identify columns of
    the ORIGINAL matrix that form a basis. Their reduced coordinates
    are exactly the pivot rows of RREF. No float or pseudoinverse.
    """
    if not matrix:
        raise ValueError('empty matrix cannot form tensor factor')
    columns = len(matrix[0])
    if columns == 0 or any(len(row) != columns for row in matrix):
        raise ValueError('invalid tensor factor matrix')
    rows = len(matrix)
    if rows * columns > budget.limits.max_core_entries:
        raise CapacityError('ETH tensor factor matrix entry limit')
    reduced = [row.copy() for row in matrix]
    pivots: list[int] = []
    for column in range(columns):
        rank = len(pivots)
        pivot = next((j for j in range(rank, rows)
                      if reduced[j][column]), None)
        if pivot is None:
            continue
        reduced[rank], reduced[pivot] = reduced[pivot], reduced[rank]
        scale = reduced[rank][column]
        reduced[rank] = [
            budget.div(element, scale) for element in reduced[rank]
        ]
        for j in range(rows):
            if j != rank:
                multiple = reduced[j][column]
                if multiple:
                    reduced[j] = [
                        budget.sub(a, budget.mul(multiple, b))
                        for a, b in zip(reduced[j], reduced[rank])
                    ]
        pivots.append(column)
        if len(pivots) == min(rows, columns):
            break
    independent = [
        [matrix[i][j] for j in pivots] for i in range(rows)
    ]
    coefficients = reduced[:len(pivots)]
    return independent, coefficients


def _compress(train: _Train, domains: tuple[int, ...],
              budget: _Budget) -> _Train:
    """Left and right exact rational rank sweeps, no numerical threshold."""
    if len(train) < 2:
        return train
    cores: list[list[list[list[Fraction]]]] = [
        [[list(row) for row in matrix] for matrix in core] for core in train
    ]
    for g in range(len(cores) - 1):
        domain, left, right = (len(cores[g]), len(cores[g][0]),
                               len(cores[g][0][0]))
        flat = [
            [cores[g][x][l][j] for j in range(right)]
            for l in range(left) for x in range(domain)
        ]
        independent, coefficient = _column_factor(flat, budget)
        rank = len(coefficient)
        if not rank:
            return _zeros(domains)
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
            raise ArithmeticError('tensor bond mismatch during left sweep')
        budget.core(next_domain, rank, next_right, before=False)
        cores[g + 1] = [
            [[_dot(coefficient[k],
                   [cores[g + 1][x][j][z] for j in range(right)], budget)
              for z in range(next_right)]
             for k in range(rank)]
            for x in range(next_domain)
        ]
        for matrix in cores[g + 1]:
            for row in matrix:
                for value in row:
                    budget.check(value)

    for g in range(len(cores) - 1, 0, -1):
        domain, left, right = _dimensions(tuple(
            tuple(tuple(row) for row in matrix) for matrix in cores[g]))
        transposed = [
            [cores[g][x][k][z] for k in range(left)]
            for x in range(domain) for z in range(right)
        ]
        independent, coefficient = _column_factor(transposed, budget)
        rank = len(coefficient)
        if not rank:
            return _zeros(domains)
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
            raise ArithmeticError('tensor bond mismatch during right sweep')
        budget.core(previous_domain, previous_left, rank, before=False)
        cores[g - 1] = [
            [[_dot(cores[g - 1][x][k], coefficient[z], budget)
              for z in range(rank)]
             for k in range(previous_left)]
            for x in range(previous_domain)
        ]
        for matrix in cores[g - 1]:
            for row in matrix:
                for value in row:
                    budget.check(value)

    return tuple(
        tuple(tuple(tuple(row) for row in matrix) for matrix in core)
        for core in cores
    )


def _hadamard(
    left: _Train, right: _Train, domains: tuple[int, ...], budget: _Budget,
) -> _Train:
    """Pointwise product of tensor trains via corewise Kronecker products."""
    result: list[_Core] = []
    for g, (a, b) in enumerate(zip(left, right)):
        domain, la, ra = _dimensions(a)
        other_domain, lb, rb = _dimensions(b)
        if domain != other_domain or domain != domains[g]:
            raise ArithmeticError('tensor physical domain mismatch')
        budget.core(domain, la * lb, ra * rb, before=True)
        core = tuple(
            tuple(
                tuple(
                    budget.mul(a[x][i][j], b[x][k][z])
                    for j in range(ra) for z in range(rb)
                )
                for i in range(la) for k in range(lb)
            )
            for x in range(domain)
        )
        result.append(core)
    return tuple(result)


def _clause_train(
    clause: tuple[int, ...], occurrences: tuple[object, ...],
    owner: int, design: MeasurementDesign, domains: tuple[int, ...],
    budget: _Budget,
) -> _Train:
    """Exact 2**w+1-state automaton for 1 - product of false literals.

    For each literal j, its false-value f_j is a sum over groups g of
    local terms a_(j,g)(x_g). A state records which literals have already
    selected a group to contribute their term. Choosing disjoint new
    subsets at successive groups enumerates the product of sums
    implicitly, once per term assignment.
    """
    from .design import CertifiedOccurrence

    typed = tuple(occ for occ in occurrences if isinstance(occ, CertifiedOccurrence))
    if len(typed) != len(occurrences) or len(clause) != len(typed):
        raise ArithmeticError('uncertified literal occurrence in tensor clause')
    width = len(clause)
    if width == 0:
        return _zeros(domains)
    states = 1 << width
    constant_state = states
    full = states - 1
    train: list[_Core] = []
    for g, (group, rows, domain) in enumerate(
        zip(design.groups, design.matrices, domains)
    ):
        left = 1 if g == 0 else states + 1
        right = 1 if g == len(domains) - 1 else states + 1
        budget.core(domain, left, right, before=True)
        matrices: list[_Matrix] = []
        for mask in range(domain):
            coeffs: list[Fraction] = []
            for literal, occurrence in zip(clause, typed):
                if g == owner:
                    linear = Fraction(0)
                    for j, coefficient in enumerate(occurrence.local):
                        if mask & (1 << j):
                            linear = budget.add(linear, coefficient)
                    local = Fraction(int(literal > 0)) - linear if literal > 0 else linear
                else:
                    measurement = tuple(
                        sum(coefficient for j, coefficient in enumerate(row)
                            if mask & (1 << j))
                        for row in rows
                    )
                    linear = Fraction(0)
                    for coefficient, observed in zip(
                        occurrence.lambda_by_group[g], measurement,
                    ):
                        linear = budget.add(
                            linear, budget.mul(coefficient, Fraction(observed)))
                    local = -linear if literal > 0 else linear
                coeffs.append(budget.check(local))

            def transition(source: int, target: int) -> Fraction:
                if source == constant_state or target == constant_state:
                    return Fraction(int(source == target == constant_state))
                if source & target != source:
                    return Fraction(0)
                product_value = Fraction(1)
                for j in range(width):
                    if (target ^ source) & (1 << j):
                        product_value = budget.mul(product_value, coeffs[j])
                return product_value

            matrix: list[tuple[Fraction, ...]] = []
            for left_index in range(left):
                source_states = ((0, -1), (constant_state, 1)) if g == 0 else ((left_index, 1),)
                row: list[Fraction] = []
                for right_index in range(right):
                    targets = ((full, 1), (constant_state, 1)) if g == len(domains) - 1 else ((right_index, 1),)
                    value = Fraction(0)
                    for source, sign in source_states:
                        for target, scale in targets:
                            value = budget.add(value, budget.mul(
                                Fraction(sign * scale), transition(source, target)
                            ))
                    row.append(value)
                matrix.append(tuple(row))
            matrices.append(tuple(matrix))
        train.append(tuple(matrices))
    return tuple(train)


def _sum_all(train: _Train, budget: _Budget) -> Fraction:
    vector = [Fraction(1)]
    for core in train:
        _, left, right = _dimensions(core)
        if len(vector) != left:
            raise ArithmeticError('tensor summation bond mismatch')
        output = [Fraction(0) for _ in range(right)]
        for matrix in core:
            for i in range(left):
                if vector[i]:
                    for j in range(right):
                        output[j] = budget.add(
                            output[j], budget.mul(vector[i], matrix[i][j]))
        vector = output
    if len(vector) != 1:
        raise ArithmeticError('tensor summation did not terminate')
    return vector[0]


def contract_certified_order_zero(
    formula: CNFFormula,
    design: MeasurementDesign,
    replacements: ReplacementSystem | None = None,
    *, at: Rational,
    limits: TensorLimits = TensorLimits(),
) -> TensorContractionResult:
    """Exact H(at) via bounded low-rank factor contraction and certificates.

    Order-0 only. This does not provide higher Taylor coefficients or
    count recovery for a nonconstant replacement without Hermite data.
    """
    groups = design.groups
    if len(groups) > limits.max_groups:
        raise CapacityError('ETH tensor group count limit')
    if len(formula.clauses) > limits.max_clauses:
        raise CapacityError('ETH tensor clause count limit')
    if sum(map(len, design.matrices)) > limits.max_measurement_rows:
        raise CapacityError('ETH tensor measurement row count limit')
    # Refuse before even exponentiating a huge supplied group size or
    # performing the expensive center-specific certificate.
    if any(len(group) >= limits.max_group_masks.bit_length()
           for group in groups):
        raise CapacityError('ETH tensor local group-mask limit')
    domains = tuple(1 << len(group) for group in groups)
    if any(domain > limits.max_group_masks for domain in domains):
        raise CapacityError('ETH tensor local group-mask limit')
    if replacements is None:
        replacements = ReplacementSystem.identity(formula)
    certificate = certify_measurements(formula, replacements, design, at=at)
    budget = _Budget(limits)
    state = _ones(domains)
    history: list[tuple[int, ...]] = []
    for clause, certified, owner in zip(
        formula.clauses, certificate.occurrences, design.clause_groups
    ):
        local = _clause_train(clause, certified, owner, design, domains, budget)
        local = _compress(local, domains, budget)
        state = _hadamard(state, local, domains, budget)
        state = _compress(state, domains, budget)
        history.append(_bonds(state))
    final = _sum_all(state, budget)
    return TensorContractionResult(
        center=certificate.center,
        value=final,
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
