"""ETH-003: exact, manually supplied measurement-separation certificates.

Implements the four conditions in the October 25 manuscript's
(r, tau, D)-design definition at a *fixed* interpolation center.
No low-degree design constructor or asymptotic parameter schedule is claimed.
Variables and groups are indexed from zero in this Python API.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from .backends import ArithmeticBackend, check_arithmetic_backend, flint_row_combination
from .cnf import CNFFormula
from .polynomial import Rational, ReplacementSystem, _exact_fraction


@dataclass(frozen=True, slots=True)
class MeasurementDesign:
    """Variable partition, clause ownership and shared integer measurements.

    ``groups[g]`` lists zero-based variable indices. ``clause_groups[e]``
    assigns clause e to one group. ``matrices[g]`` contains integer rows
    over that group's variables, in the *same column order* as ``groups[g]``.
    ``tau`` and ``D`` are explicit rational/integer certificate bounds.
    """

    groups: tuple[tuple[int, ...], ...]
    clause_groups: tuple[int, ...]
    matrices: tuple[tuple[tuple[int, ...], ...], ...]
    tau: Fraction
    D: int


@dataclass(frozen=True, slots=True)
class CertifiedOccurrence:
    """A replacement at the center, decomposed into local and shared parts."""

    local: tuple[Fraction, ...]
    lambda_by_group: tuple[tuple[Fraction, ...], ...]


@dataclass(frozen=True, slots=True)
class MeasurementCertificate:
    """Constructively verified exact rational witnesses for all clauses."""

    center: Fraction
    design: MeasurementDesign
    occurrences: tuple[tuple[CertifiedOccurrence, ...], ...]
    total_measurements: int


def _row_combination(
    rows: tuple[tuple[int, ...], ...], target: tuple[Fraction, ...],
) -> tuple[Fraction, ...]:
    """Return lambdas with sum(lambda_i * rows[i]) == target, or refuse.

    Exact Gauss-Jordan on C^transpose lambda = target; free lambdas are zero.
    Handles empty matrices and rank-deficient/repeated rows without floats.
    """
    width = len(target)
    nrows = len(rows)
    if any(len(row) != width for row in rows):
        raise ValueError('measurement matrix width mismatch')
    augmented = [
        [Fraction(rows[j][i]) for j in range(nrows)] + [target[i]]
        for i in range(width)
    ]
    pivot_columns: list[int] = []
    pivot_row = 0
    for column in range(nrows):
        pivot = next((i for i in range(pivot_row, width) if augmented[i][column]), None)
        if pivot is None:
            continue
        augmented[pivot_row], augmented[pivot] = augmented[pivot], augmented[pivot_row]
        scale = augmented[pivot_row][column]
        augmented[pivot_row] = [value / scale for value in augmented[pivot_row]]
        for row_idx in range(width):
            if row_idx == pivot_row:
                continue
            factor = augmented[row_idx][column]
            if factor:
                augmented[row_idx] = [
                    a - factor * b
                    for a, b in zip(augmented[row_idx], augmented[pivot_row])
                ]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == width:
            break
    if any(not any(row[:nrows]) and row[nrows] for row in augmented):
        raise ValueError('cross-group vector outside measurement row space')
    solution = [Fraction(0) for _ in range(nrows)]
    for i, column in enumerate(pivot_columns):
        solution[column] = augmented[i][nrows]
    # Explicitly reconstruct the input: the witness is a checkable certificate.
    if any(sum((solution[j] * rows[j][i] for j in range(nrows)), Fraction(0)) != target[i]
           for i in range(width)):
        raise ValueError('cross-group vector outside measurement row space')
    return tuple(solution)


def certify_measurements(
    formula: CNFFormula,
    replacements: ReplacementSystem,
    design: MeasurementDesign,
    *,
    at: Rational, backend: ArithmeticBackend = "python",
) -> MeasurementCertificate:
    """Verify all four design conditions and compute exact lambda witnesses.

    The certificate applies only at ``at``. It does not establish a design at
    other interpolation centers or construct the paper's parameters.
    """
    check_arithmetic_backend(backend)
    center = _exact_fraction(at)
    replacements.validate(formula)
    r = len(design.groups)
    n = formula.nvars
    if not r or len(design.matrices) != r:
        raise ValueError('every group needs a measurement matrix')
    if len(design.clause_groups) != len(formula.clauses):
        raise ValueError('every clause needs one assigned group')
    if type(design.D) is not int or design.D < 0:
        raise ValueError('D must be a nonnegative integer')
    tau = _exact_fraction(design.tau)
    if tau < 0:
        raise ValueError('tau must be nonnegative')
    if any(type(index) is not int or index < 0 or index >= n
           for group in design.groups for index in group):
        raise ValueError('variable index outside declared CNF')
    flattened = [index for group in design.groups for index in group]
    if len(flattened) != n or len(set(flattened)) != n:
        raise ValueError('groups must partition all declared variables exactly once')
    if any(len(group) * r > 2 * n for group in design.groups):
        raise ValueError('group exceeds paper small-group bound |S_g| <= 2n/r')
    if any(type(group) is not int or not 0 <= group < r for group in design.clause_groups):
        raise ValueError('invalid clause assigned group')
    total_measurements = 0
    for group, rows in zip(design.groups, design.matrices):
        total_measurements += len(rows)
        for row in rows:
            if len(row) != len(group):
                raise ValueError('measurement matrix width mismatch')
            if any(type(entry) is not int for entry in row):
                raise ValueError('measurement coefficients must be integers')
            if sum(abs(entry) for entry in row) > design.D:
                raise ValueError('measurement row exceeds L1 bound D')
    if total_measurements > 2 * tau * n:
        raise ValueError('total measurement rows exceed 2*tau*n')

    certified: list[tuple[CertifiedOccurrence, ...]] = []
    for e, forms in enumerate(replacements.clauses):
        owner = design.clause_groups[e]
        compiled: list[CertifiedOccurrence] = []
        for form in forms:
            coefficients = tuple(polynomial.evaluate(center) for polynomial in form.coefficients)
            local = tuple(coefficients[index] for index in design.groups[owner])
            by_group: list[tuple[Fraction, ...]] = []
            for h, (group, rows) in enumerate(zip(design.groups, design.matrices)):
                if h == owner:
                    by_group.append(())
                else:
                    vector = tuple(coefficients[index] for index in group)
                    by_group.append(flint_row_combination(rows, vector) if backend == 'flint'
                                    else _row_combination(rows, vector))
            compiled.append(CertifiedOccurrence(local=local, lambda_by_group=tuple(by_group)))
        certified.append(tuple(compiled))
    return MeasurementCertificate(
        center=center, design=design, occurrences=tuple(certified),
        total_measurements=total_measurements,
    )
