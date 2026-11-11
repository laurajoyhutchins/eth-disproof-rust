"""Source-correlated conditional bounds for the original separated Taylor path.

Not a bound on the *capped* implementation's all-input runtime, construction
admission, or the Lean primitive machine.  For a supplied certified design,
this audits the exact outer loop geometry of eth/taylor.py's summation='tuples'
and a deliberately loose *common-denominator* bound for its intermediate
rational jets, not merely for the final answer.

Actual interpreter overhead, sparse-design construction, certificate solving,
fixed-cap refusals, and downstream Hermite reconstruction are NOT included.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb

from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.design import MeasurementCertificate
from non_exponential_sudoku.eth.paper_admitted_witness import (
    virtual_coupled_3cnf_step5,
)
from non_exponential_sudoku.eth.polynomial import ReplacementSystem


def ceil_log2(value: int) -> int:
    if type(value) is not int or value < 1:
        raise ValueError("positive integer required")
    return (value - 1).bit_length()


def ceil_log2_ratio(numerator: int, denominator: int) -> int:
    """Ceiling log2(a/b) for a>=b>0, with no floating point."""
    if (type(numerator) is not int or type(denominator) is not int
            or denominator < 1 or numerator < denominator):
        raise ValueError("require positive integral ratio at least one")
    result = max(0, numerator.bit_length() - denominator.bit_length())
    while (denominator << result) < numerator:
        result += 1
    return result


def _bits(value: Fraction) -> int:
    return max(1, abs(value.numerator).bit_length(),
               value.denominator.bit_length())


@dataclass(frozen=True, slots=True)
class SeparatedCenterEnvelope:
    """Finite, source-matched bound for one already certified center.

    `loop_assignment_slots` bounds the exact group-mask visits in
    `_TaylorEvaluator.restricted`. The loops can skip tuples on early
    zero, so observed visits may be smaller. The rational ceiling uses
    a single common denominator of input coefficients and witness scalars.
    """

    variables: int
    clauses: int
    occurrences: int
    groups: int
    measurement_rows: int
    measurement_range: int
    order: int
    max_replacement_degree: int
    input_rational_count: int
    max_input_rational_bits: int
    taylor_pairs: int
    tuples_per_pair: int
    group_masks_per_tuple: int
    loop_assignment_slots: int
    clause_evaluations_upper: int
    rational_jet_operation_upper: int
    common_denominator_bits_upper: int
    every_intermediate_fraction_bits_upper: int
    retained_rational_slots_upper: int
    abstract_schoolbook_bit_work_upper: int

    @property
    def log2_bit_work_upper(self) -> int:
        return ceil_log2(self.abstract_schoolbook_bit_work_upper)


def certified_separated_center_envelope(
    formula: CNFFormula, replacements: ReplacementSystem,
    certificate: MeasurementCertificate, *, order: int, cache_entries: int = 64,
) -> SeparatedCenterEnvelope:
    """Charge all source loops, source-limited caches and rational jet heights.

    The *input* certificate has already passed certify_measurements.
    For every source intermediate, denominators divide H**((d+1)*ell),
    where H is the product of denominators of every replacement coefficient,
    center, local measurement coefficient, and lambda witness coefficient.
    At most ell literal polynomials contribute to a product, and sums over
    pairs, y, and masks enlarge numerator length only logarithmically.

    This is a constructive overestimate of the *mathematical* evaluator's
    integer bit work using schoolbook Fraction primitives. It does not
    count CPython object allocation or certificate construction.
    """
    if (type(order) is not int or order < 0 or order > formula.nvars
            or type(cache_entries) is not int or cache_entries < 1):
        raise ValueError("require 0<=order<=n and positive finite cache")
    if formula.nvars < 1 or not formula.clauses:
        raise ValueError("require nonempty normalized CNF")
    replacements.validate(formula)
    design = certificate.design
    n, m = formula.nvars, len(formula.clauses)
    if (len(design.clause_groups) != m
            or len(design.groups) != len(design.matrices)
            or sum(map(len, design.groups)) != n):
        raise ValueError("malformed supplied design geometry")
    if design.D < 0:
        raise ValueError("measurement L1 bound must be nonnegative")
    ell = sum(len(clause) for clause in formula.clauses)
    if not ell:
        raise ValueError("nonempty clauses must contain literals")
    if len(certificate.occurrences) != m:
        raise ValueError("certificate clause count mismatch")
    s = certificate.total_measurements
    if s != sum(map(len, design.matrices)):
        raise ValueError("certificate measurement count mismatch")

    # Fraction source scalars, including every polynomial coefficient and
    # independently constructed lambda/local witness. Count repeated
    # denominators separately: the product remains a common multiple.
    rational_count = 1
    bits = _bits(certificate.center)
    d = 0
    for rows in replacements.clauses:
        for form in rows:
            for polynomial in form.coefficients:
                d = max(d, polynomial.degree)
                for coefficient in polynomial.coefficients:
                    rational_count += 1
                    bits = max(bits, _bits(coefficient))
    for rows in certificate.occurrences:
        for witness in rows:
            for value in witness.local:
                rational_count += 1
                bits = max(bits, _bits(value))
            for group in witness.lambda_by_group:
                for value in group:
                    rational_count += 1
                    bits = max(bits, _bits(value))

    common_bits = rational_count * bits
    P = sum(comb(n, j) * (1 << j) for j in range(min(n, order) + 1))
    Y = (2 * design.D + 1) ** s
    masks = tuple(1 << len(group) for group in design.groups)
    A = sum(masks)
    per_group_clauses = [0] * len(masks)
    for g in design.clause_groups:
        per_group_clauses[g] += 1
    weighted = sum(a * c for a, c in zip(masks, per_group_clauses))
    loops = P * Y * A
    clauses_upper = P * Y * weighted

    # Horner coefficient of P(t+z) is a sum of at most (d+1) terms:
    # c_h * binom(h,j) * t**(h-j). Its denominator divides H**(d+1).
    shift_bits = ((d + 1) * (common_bits + bits) + d
                  + ceil_log2(d + 1) + 4)
    # A correction sums <=n zero-constant shifts; a base sums <=n+s
    # local/witness terms, each weighted by |y_i|<=D.
    correction_bits = shift_bits + ceil_log2(n + 1) + 3
    base_bits = ((d + 1) * common_bits + bits
                 + ceil_log2(n + s + 1) + ceil_log2(design.D + 1) + 4)
    literal_bits = max(correction_bits, base_bits, (d + 1) * common_bits) + 5
    # Products of <=ell literal jets and m subtractions of these products.
    # Convolutions introduce <=(order+1)**ell additive contributions.
    # The final nested sums have <= P*Y*2**n summands, and every source
    # prefix product and partial sum is bounded by the same envelope.
    numerator_bits = (ell * (literal_bits + ceil_log2(order + 1) + 4)
                      + 3 * m + n + ceil_log2(P) + ceil_log2(Y) + 16)
    denominator_bits = (d + 1) * ell * common_bits + 3
    fraction_bits = max(numerator_bits, denominator_bits) + 6

    # A conservative source-loop polynomial multiplier: each visited
    # assignment scans at most n+s+ell+m+order+d coordinates and performs
    # truncated jet operations of at most (order+1)**2 scalar operations.
    # Also charge all source precomputation and pair-specific corrections.
    size = n + m + ell + s + order + d + cache_entries + 4
    outer = P * Y * (A + weighted + len(masks) + 1)
    preprocessing = (ell * n * (d + 1) + P * ell * n + 1)
    source_ops = 64 * (outer + preprocessing + 1) * size**4
    # Euclidean rational normalization and schoolbook arithmetic on
    # fractions <= fraction_bits uses <= O(fraction_bits**3) bit work.
    bit_work = source_ops * max(2, fraction_bits) ** 3
    # Dense source replacements, O(ell*n) shifted jets, a fixed bounded
    # correction cache, one y tuple, one group-mask assignment, the
    # certificate and its group rows. Constant 256 FLINT cache is also
    # covered. This bounds *rational coordinate slots*, not CPython heap.
    scalar_slots = 64 * (
        ell * n * (d + order + 3)
        + cache_entries * ell * (order + 1)
        + ell * (n + s + 1)
        + s * n + n * n + m + n + s + 256 * (order + 1) + 1
    )
    return SeparatedCenterEnvelope(
        variables=n, clauses=m, occurrences=ell,
        groups=len(masks), measurement_rows=s,
        measurement_range=design.D, order=order,
        max_replacement_degree=d,
        input_rational_count=rational_count,
        max_input_rational_bits=bits,
        taylor_pairs=P, tuples_per_pair=Y, group_masks_per_tuple=A,
        loop_assignment_slots=loops, clause_evaluations_upper=clauses_upper,
        rational_jet_operation_upper=source_ops,
        common_denominator_bits_upper=common_bits,
        every_intermediate_fraction_bits_upper=fraction_bits,
        retained_rational_slots_upper=scalar_slots,
        abstract_schoolbook_bit_work_upper=bit_work,
    )


@dataclass(frozen=True, slots=True)
class PaperSeparatedRate:
    """Exponent/n for a conservative source-loop bound at n=2**lambda.

    The finite +ceil(log2(n+1))+ceil(log2(r)) additive exponents are
    separate, because n itself would be astronomical. This is an upper
    rate, not a measured cost or an exact complexity exponent.
    """

    lambda_bits: int
    r: int
    Q: int
    R: int
    order_fraction_upper: Fraction
    pair_rate_upper: Fraction
    measurement_rate_upper: Fraction
    group_rate_upper: Fraction
    total_rate_upper_without_additive_over_n: Fraction
    additive_exponent_upper: int


def paper_separated_rate(lambda_bits: int) -> PaperSeparatedRate:
    """Derive 2**(n*rate + additive) without allocating n=2**lambda.

    Under the manuscript Step-5 sufficient admission:
        q<=3nR/Q, q/n<=delta=3R/Q<=1/2
        P<= (n+1) * 2**(n*delta*ceil(log2(6/delta)))
        s<=2n/(r*lambda); D<=r**(2Q)
        Y<=(2D+1)**s; A<=r*2**(2n/r).
    The 6/delta ceiling replaces 2e/delta by an integer inequality.
    """
    witness = virtual_coupled_3cnf_step5(lambda_bits)
    if not witness.admitted_by_sufficient_conditions:
        raise ValueError("Step-5 sufficient inequalities not certified")
    r, Q, R = witness.r, witness.Q, witness.R
    delta = Fraction(3 * R, Q)
    if delta > Fraction(1, 2):
        raise ArithmeticError("certified Step-5 Taylor fraction exceeds half")
    pair = delta * ceil_log2_ratio(2 * Q, R)
    measurement = Fraction(2 * (2 * Q * r.bit_length() + 2), r * lambda_bits)
    group = Fraction(2, r)
    return PaperSeparatedRate(
        lambda_bits, r, Q, R, delta, pair, measurement, group,
        pair + measurement + group,
        lambda_bits + 1 + ceil_log2(r),
    )
