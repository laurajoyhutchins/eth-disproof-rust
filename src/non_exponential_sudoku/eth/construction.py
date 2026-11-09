"""Bounded constructive instances of the October 25 auxiliary ETH design.

Implements the manuscript's auxiliary swap/spectral construction (overview
Steps 1--3) and its occurrence-to-coordinate transfer (Step 4). Automatic
schedules include the exact conditional-expectation derandomization and an
illustrative digit schedule. The strict paper-parameter entrypoint refuses
when its quantitative prerequisites are absent. All output designs are
independently certified at each center. This is not a practical general
subexponential #SAT implementation.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction
from itertools import combinations, product
from math import comb, floor
from typing import Literal, Sequence

from non_exponential_sudoku.runtime.budget import CapacityError

from .backends import ArithmeticBackend
from .balance import BalanceLimits, BalancedSchedules, choose_balanced_schedules
from .cnf import CNFFormula
from .design import MeasurementDesign, certify_measurements
from .polynomial import ONE, ZERO, Polynomial, ReplacementForm, ReplacementSystem
from .parameters import (PaperAdmission, audit_bounded_cnf)


@dataclass(frozen=True, slots=True)
class ConstructionLimits:
    """Explicit caps for the dense auxiliary research construction."""

    max_dimension: int = 64
    max_variables: int = 64
    max_clauses: int = 128
    max_auxiliary_cells: int = 4096
    max_measurement_rows: int = 128
    max_occurrences: int = 64
    max_coeff_bits: int = 4096

    def __post_init__(self) -> None:
        for name in self.__dataclass_fields__:
            if type(getattr(self, name)) is not int or getattr(self, name) < 1:
                raise ValueError(f'{name} must be a positive integer')


@dataclass(frozen=True, slots=True)
class AuxiliaryDesign:
    """Spectral interpolation, measurement rows, and polynomial replacement rows.

    Coordinates are Q pairs (a,d) of zero-based group IDs, lexicographically
    ordered. ``rows[u][w]`` is the exact coefficient of auxiliary coordinate
    w in the replacement of coordinate u.
    """

    r: int
    Q: int
    R: int
    interval: tuple[int, ...]
    labels: tuple[tuple[tuple[int, int], ...], ...]
    measurements: tuple[tuple[int, ...], ...]
    rows: tuple[tuple[Polynomial, ...], ...]
    max_polynomial_degree: int

    @property
    def dimension(self) -> int:
        return len(self.labels)


@dataclass(frozen=True, slots=True)
class ConstructedDesigns:
    """Verified construction with separately recorded paper admission."""

    replacements: ReplacementSystem
    centers: tuple[tuple[int, MeasurementDesign], ...]
    auxiliary: AuxiliaryDesign
    variable_schedules: tuple[tuple[int, ...], ...]
    clause_schedules: tuple[tuple[int, ...], ...]
    label_multiplicity: int
    max_measurement_rows: int
    algorithm_status: str = 'bounded-constructive-reference; no asymptotic guarantee'
    balancing: BalancedSchedules | None = None
    paper_admission: PaperAdmission | None = None


def _interpolation_polynomial(points: tuple[int, ...]) -> Polynomial:
    """Alternating values on consecutive integers in the Newton basis.

    Delta**k (-1)**(a+j) at j=0 is (-1)**a * (-2)**k.
    This avoids repeatedly constructing full Lagrange basis polynomials.
    """
    if not points or any(point != points[0] + i for i, point in enumerate(points)):
        raise ValueError('spectral interpolation points must be consecutive')
    start = points[0]
    result = ZERO
    basis = ONE
    for order in range(len(points)):
        result = result + basis.scale((-1 if start % 2 else 1) * (-2) ** order)
        if order + 1 < len(points):
            basis = (basis * Polynomial((Fraction(-start - order), Fraction(1)))).scale(
                Fraction(1, order + 1))
    return result


def _walsh_coefficients(polynomial: Polynomial, Q: int) -> dict[int, Fraction]:
    """Sparse Walsh coefficients of f(popcount(mask)), grouped by Hamming weight.

    All masks of the same cardinality share one coefficient.  The s-th
    coefficient is (-1)**s / 2**Q times a binomially weighted sum of
    the s-th forward differences of f on 0..Q.  It vanishes for
    s > degree(f).  No 2**Q x 2**Q Fourier transform is constructed.
    """
    if type(Q) is not int or Q < 0:
        raise ValueError('Q must be a nonnegative integer')
    differences = [polynomial.evaluate(j) for j in range(Q + 1)]
    coefficients: dict[int, Fraction] = {}
    for cardinality in range(min(Q, polynomial.degree) + 1):
        value = sum(
            (comb(Q - cardinality, j) * term
             for j, term in enumerate(differences)), Fraction(0),
        ) / (1 << Q)
        if cardinality % 2:
            value = -value
        if value:
            for positions in combinations(range(Q), cardinality):
                coefficients[sum(1 << position for position in positions)] = value
        differences = [right - left for left, right in
                       zip(differences, differences[1:])]
    return coefficients


def _local_eigenvectors(r: int) -> tuple[tuple[tuple[int, ...], bool], ...]:
    """Integral orthogonal eigenbasis of a swap on [r] x [r]."""
    basis: list[tuple[tuple[int, ...], bool]] = []
    for a in range(r):
        v = [0] * (r * r)
        v[a * r + a] = 1
        basis.append((tuple(v), False))
    for a in range(r):
        for b in range(a + 1, r):
            plus = [0] * (r * r)
            plus[a * r + b] = 1
            plus[b * r + a] = 1
            basis.append((tuple(plus), False))
            minus = plus.copy()
            minus[b * r + a] = -1
            basis.append((tuple(minus), True))
    return tuple(basis)


def _bit_size(poly: Polynomial) -> int:
    return max((max(abs(c.numerator).bit_length(), c.denominator.bit_length())
                for c in poly.coefficients), default=0)


def construct_auxiliary(
    *, r: int, Q: int, R: int, limits: ConstructionLimits = ConstructionLimits(),
) -> AuxiliaryDesign:
    """Construct Steps 1--3 with rational Walsh coefficients and exact checks.

    R consecutive spectral interpolation points produce degree <= R-1
    replacements.  The exceptional tensor eigenvectors are shared integer
    measurement rows.  Dense dimension is intentionally capped.
    """
    if any(type(x) is not int for x in (r, Q, R)) or r < 2 or Q < 1 or not 1 <= R <= Q + 1:
        raise ValueError('require r>=2, Q>=1, and 1<=R<=Q+1')
    D = r ** (2 * Q)
    if D > limits.max_dimension or D * D > limits.max_auxiliary_cells:
        raise CapacityError('ETH auxiliary dense dimension limit')
    p = Fraction(r - 1, 2 * r)
    a0 = floor(Q * p - Fraction(R - 1, 2))
    a0 = max(0, min(Q - R + 1, a0))
    interval = tuple(range(a0, a0 + R))
    f = _interpolation_polynomial(interval)
    if f.degree > R - 1:
        raise ArithmeticError('spectral interpolation exceeds degree bound')

    labels = tuple(tuple((coord[2 * s], coord[2 * s + 1]) for s in range(Q))
                   for coord in product(range(r), repeat=2 * Q))
    lookup = {label: i for i, label in enumerate(labels)}
    basis = _local_eigenvectors(r)
    measured: list[tuple[int, ...]] = []
    for selected in product(range(len(basis)), repeat=Q):
        negs = sum(basis[j][1] for j in selected)
        if negs in interval:
            continue
        vector = tuple(
            _tensor_entry(label, selected, basis, r) for label in labels
        )
        measured.append(vector)
    if len(measured) > limits.max_measurement_rows:
        raise CapacityError('ETH auxiliary exceptional direction limit')

    # Fourier/Walsh expansion of f(W).  The transform depends only on
    # subset cardinality; a full 4**Q pair enumeration is unnecessary.
    betas = _walsh_coefficients(f, Q)
    if any(mask.bit_count() > R - 1 for mask in betas):
        raise ArithmeticError('spectral support violates degree bound')

    rows: list[tuple[Polynomial, ...]] = []
    max_degree = 0
    for u, label in enumerate(labels):
        matrix_row = [Fraction(0) for _ in range(D)]
        for mask_s, coefficient in betas.items():
            mapped = tuple((a, d) if mask_s & (1 << s) else (d, a)
                           for s, (a, d) in enumerate(label))
            matrix_row[lookup[mapped]] += coefficient
        out: list[Polynomial] = []
        for w, target in enumerate(labels):
            m = matrix_row[w]
            if not m:
                poly = ONE if w == u else ZERO
            else:
                exceptions = [s + 1 for s in range(Q)
                              if target[s][0] != label[s][1]]
                if len(exceptions) > R - 1:
                    raise ArithmeticError('auxiliary support outside permitted swaps')
                phi = ONE
                for s in exceptions:
                    phi = phi * Polynomial((Fraction(1), Fraction(-1, s)))
                poly = Polynomial.constant(1 if w == u else 0) - Polynomial.constant(m)
                poly = poly + phi.scale(m)
            if _bit_size(poly) > limits.max_coeff_bits:
                raise CapacityError('ETH auxiliary rational coefficient limit')
            max_degree = max(max_degree, poly.degree)
            if poly.at_zero != (1 if w == u else 0):
                raise ArithmeticError('auxiliary P(0) identity failed')
            out.append(poly)
        rows.append(tuple(out))
    return AuxiliaryDesign(r, Q, R, interval, labels, tuple(measured), tuple(rows), max_degree)


def _tensor_entry(
    label: tuple[tuple[int, int], ...], selected: tuple[int, ...],
    basis: tuple[tuple[tuple[int, ...], bool], ...], r: int,
) -> int:
    value = 1
    for (a, d), j in zip(label, selected):
        value *= basis[j][0][a * r + d]
    return value


def deterministic_schedules(
    formula: CNFFormula, *, r: int, Q: int,
) -> tuple[tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]]:
    """Small-instance schedules, not conditional-expectation derandomization.

    Deterministic base-r digits spread variable and clause group choices.
    This does NOT establish the manuscript's label-multiplicity bound.
    """
    if r < 2 or Q < 1 or formula.nvars < r:
        raise ValueError('schedules require nvars >= r >= 2 and Q>=1')
    a = tuple(tuple(((v // (r ** s)) + (v // (r ** Q)) + s) % r
                    for s in range(Q)) for v in range(formula.nvars))
    d = tuple(tuple(((e // (r ** s)) + (e // (r ** Q)) + s + 1) % r
                    for s in range(Q)) for e in range(len(formula.clauses)))
    return a, d


def construct_from_schedules(
    formula: CNFFormula, auxiliary: AuxiliaryDesign,
    variable_schedules: Sequence[Sequence[int]],
    clause_schedules: Sequence[Sequence[int]],
    *, limits: ConstructionLimits = ConstructionLimits(),
) -> ConstructedDesigns:
    """Transfer Step 4, split measurements by group, certify every center.

    Copies of B are introduced for colliding incidence labels, each with at
    most one variable at any coordinate.  This preserves counts at T=0.
    The returned tau is the ACTUAL row count bound, not the paper's tau.
    """
    n, r, Q = formula.nvars, auxiliary.r, auxiliary.Q
    if n < r:
        raise ValueError('small-instance construction needs nvars >= r')
    if n > limits.max_variables or len(formula.clauses) > limits.max_clauses:
        raise CapacityError('ETH transferred CNF dimensions limit')
    a = tuple(tuple(seq) for seq in variable_schedules)
    d = tuple(tuple(seq) for seq in clause_schedules)
    if len(a) != n or len(d) != len(formula.clauses):
        raise ValueError('schedule count does not match variables/clauses')
    if any(len(seq) != Q or any(type(g) is not int or not 0 <= g < r for g in seq)
           for seq in (*a, *d)):
        raise ValueError('schedules must contain Q group indices in range')
    incidence_count = sum(len(clause) for clause in formula.clauses)
    if incidence_count > limits.max_occurrences:
        raise CapacityError('ETH transferred occurrence limit')
    for s in range(Q):
        if any(sum(1 for seq in a if seq[s] == g) * r > 2 * n for g in range(r)):
            raise ValueError('schedule violates small-group bound')
    lookup = {label: i for i, label in enumerate(auxiliary.labels)}
    # Allocate each occurrence in the first unused copy of its auxiliary label.
    buckets: dict[int, list[int]] = {}
    placements: list[list[tuple[int, int]]] = []
    for e, clause in enumerate(formula.clauses):
        e_places: list[tuple[int, int]] = []
        for lit in clause:
            v = abs(lit) - 1
            label = tuple((a[v][s], d[e][s]) for s in range(Q))
            u = lookup[label]
            copies = buckets.setdefault(u, [])
            copy_number = len(copies)
            copies.append(v)
            e_places.append((u, copy_number))
        placements.append(e_places)
    h = max((len(copies) for copies in buckets.values()), default=0)
    c = len(auxiliary.measurements)
    if r * h * c > limits.max_measurement_rows:
        raise CapacityError('ETH transferred measurement row limit')
    filled: list[dict[int, int]] = [dict() for _ in range(h)]
    for u, copies in buckets.items():
        for j, v in enumerate(copies):
            filled[j][u] = v
    clauses: list[tuple[ReplacementForm, ...]] = []
    for e_places in placements:
        forms: list[ReplacementForm] = []
        for u, j in e_places:
            coeffs = [ZERO for _ in range(n)]
            for w, v in filled[j].items():
                coeffs[v] = coeffs[v] + auxiliary.rows[u][w]
            if any(_bit_size(coeff) > limits.max_coeff_bits for coeff in coeffs):
                raise CapacityError('ETH transferred rational coefficient limit')
            forms.append(ReplacementForm(tuple(coeffs)))
        clauses.append(tuple(forms))
    replacements = ReplacementSystem(tuple(clauses))
    replacements.validate(formula)

    designs: list[tuple[int, MeasurementDesign]] = []
    actual_max_rows = 0
    for s in range(Q):
        groups = tuple(tuple(v for v in range(n) if a[v][s] == g) for g in range(r))
        matrices: list[tuple[tuple[int, ...], ...]] = []
        for g, group in enumerate(groups):
            rows: list[tuple[int, ...]] = []
            for filled_copy in filled:
                for C in auxiliary.measurements:
                    row = [0] * len(group)
                    for k, v in enumerate(group):
                        row[k] = sum(C[w] for w, mapped_v in filled_copy.items() if mapped_v == v)
                    rows.append(tuple(row))
            matrices.append(tuple(rows))
        actual_max_rows = max(actual_max_rows, sum(map(len, matrices)))
        bound_D = max((sum(abs(value) for value in row)
                       for matrix in matrices for row in matrix), default=0)
        row_count = sum(map(len, matrices))
        if bound_D > auxiliary.dimension:
            raise ArithmeticError('transferred row L1 exceeds auxiliary dimension')
        design = MeasurementDesign(
            groups=groups, clause_groups=tuple(seq[s] for seq in d),
            matrices=tuple(matrices), tau=Fraction(row_count, 2 * n), D=bound_D,
        )
        # This independently verifies the measurement row-space witnesses.
        certify_measurements(formula, replacements, design, at=s + 1)
        designs.append((s + 1, design))
    return ConstructedDesigns(replacements, tuple(designs), auxiliary, a, d,
                              h, actual_max_rows)


def construct_bounded_designs(
    formula: CNFFormula, *, r: int, Q: int, R: int,
    limits: ConstructionLimits = ConstructionLimits(),
    schedule: Literal['conditional', 'digits'] = 'conditional',
    balance_limits: BalanceLimits = BalanceLimits(),
) -> ConstructedDesigns:
    """Build automatically; the schedule method is explicit, never fallback.

    `conditional` implements the lemma's exact derandomization but checks
    whether its parameter hypotheses hold. `digits` is a tiny demo schedule.
    Both are resource bounded and can remain exponentially expensive.
    """
    if formula.nvars > limits.max_variables or len(formula.clauses) > limits.max_clauses:
        raise CapacityError('ETH transferred CNF dimensions limit')
    auxiliary = construct_auxiliary(r=r, Q=Q, R=R, limits=limits)
    if schedule == 'conditional':
        balanced = choose_balanced_schedules(formula, r=r, Q=Q, limits=balance_limits)
        construction = construct_from_schedules(formula, auxiliary,
                                                balanced.variable_schedules,
                                                balanced.clause_schedules, limits=limits)
        status = ('bounded-constructive-reference; conditional expectations; '
                  + ('lemma hypotheses satisfied' if balanced.lemma_hypotheses_met
                     else 'lemma hypotheses NOT satisfied'))
        return replace(construction, algorithm_status=status, balancing=balanced,
                       paper_admission=audit_bounded_cnf(formula))
    if schedule == 'digits':
        a, d = deterministic_schedules(formula, r=r, Q=Q)
        return replace(construct_from_schedules(formula, auxiliary, a, d,
                                                limits=limits),
                       paper_admission=audit_bounded_cnf(formula))
    raise ValueError('unknown ETH construction schedule')



def construct_paper_bounded_designs(
    formula: CNFFormula, *,
    limits: ConstructionLimits = ConstructionLimits(),
    balance_limits: BalanceLimits = BalanceLimits(),
) -> ConstructedDesigns:
    """Strictly admitted main-body construction for width/occurrence <=3.

    Uses ONLY the paper's explicit r,Q,R schedule and the conditional-
    expectation derandomization. If any theorem prerequisite is missing,
    refuse rather than substituting tiny demo parameters or brute force.
    Admission is necessary, not sufficient for this bounded implementation's
    resource limits. This is NOT a general-CNF path: disjoint sparsification
    remains unimplemented.
    """
    audit = audit_bounded_cnf(formula)
    audit.require()
    p = audit.parameters
    result = construct_bounded_designs(
        formula, r=p.r, Q=p.Q, R=p.R,
        schedule='conditional', limits=limits, balance_limits=balance_limits,
    )
    if result.balancing is None or not result.balancing.lemma_hypotheses_met:
        raise ArithmeticError('paper balancing lemma prerequisites lost')
    if not result.balancing.lemma_bounds_met:
        raise ArithmeticError('paper balancing lemma bounds not certified')
    # Width/occurrence and conditional-expectations checks are revalidated at
    # the entrypoint; each transferred measurement design is separately
    # certified inside construct_bounded_designs.
    if result.label_multiplicity * p.D > 2 * audit.M:
        raise ArithmeticError('paper label-multiplicity bound not achieved')
    if result.max_measurement_rows > Fraction(2 * formula.nvars, p.r * p.lambda_bits):
        raise ArithmeticError('paper total measurement bound not achieved')
    return replace(result, algorithm_status='certified main-body bounded-occurrence design',
                   paper_admission=audit)


def count_from_constructed(
    formula: CNFFormula, construction: ConstructedDesigns, *,
    order: int | None = None,
    backend: ArithmeticBackend = 'python',
    readout: Literal['origin', 'polynomial'] = 'origin',
) -> int:
    """Exact small-instance #SAT path using verified automatic center designs.

    The initial construction is part of this method's input and has no
    asymptotic resource guarantee.  This does not invoke exhaustive counting.
    Errors or resource exhaustion propagate, with no alternative solver.
    """
    from .interpolation import count_from_manual_designs, count_origin_from_manual_designs

    construction.replacements.validate(formula)
    if not construction.centers:
        raise ValueError('a constructed count needs at least one center')
    degree = sum(sum(max((coeff.degree for coeff in form.coefficients), default=0)
                         for form in row) for row in construction.replacements.clauses)
    if order is None:
        order = degree // len(construction.centers)
    if backend not in ('python', 'flint'):
        raise ValueError('backend must be python or flint')
    if readout not in ('origin', 'polynomial'):
        raise ValueError('readout must be origin or polynomial')
    count_method = (count_origin_from_manual_designs if readout == 'origin'
                    else count_from_manual_designs)
    return count_method(
        formula, construction.centers, construction.replacements,
        order=order, backend=backend,
    ).count
