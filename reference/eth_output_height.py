"""Universal final-Taylor-coefficient height lemma for exact CNF deformations.

For any valid occurrence-specific rational replacement system and any exact
rational center, every coefficient of H(center+z) has a polynomial bit-size
bound in the *encoded input* even if the number of Boolean assignments or
intermediate factor/table coefficients is exponential.

This derives a common denominator without constructing a large product,
and bounds the integer numerators by a direct expansion. It neither
constructs an admitted spectral auxiliary, bounds intermediate states,
nor proves a running-time or memory bound for an actual evaluator.

Let K be the number of explicitly stored rational coefficients of all
occurrence/variable polynomials, d their maximum degree, ell the total
number of literal occurrences, b >= 1 the maximum bit length of a
coefficient or center numerator/denominator. Let

    Q = q**d * PRODUCT(all coefficient denominators),

for center p/q in lowest terms. A coefficient of any P_e,v(p/q+z)
has denominator dividing Q. After multiplication by Q, the absolute
integer coefficient is at most

    n*(d+1) * 2**(b*(K+d)+d)

once we sum over the n variable polynomials in a false-literal form.
The constant term of 1-P adds Q, so every signed false literal has
rescaled coefficients bounded by

    A = (n*(d+1)+1)*2**(b*(K+d)+d).

Expand the m outer (1-product false) clauses. There are at most 2**m
terms per assignment, at most ell false factors per term, at most
(d+1)**ell coefficient selections, and 2**n Boolean assignments.
Writing H(p/q+z)=N(z)/Q**ell gives, for every coefficient:

  |[z**j]N| <= 2**(n+m + ell*(b*(K+d)+d
                               +ceil_log2(n*(d+1)+1)
                               +ceil_log2(d+1)))

and denominator |Q**ell| <= 2**(ell*b*(K+d)).

No interpolation, spectral parameter admission, variable elimination,
or Python Fraction size cap is assumed. The bound is deliberately loose.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.polynomial import (
    Rational, ReplacementSystem, _exact_fraction,
)


def _bits(x: int) -> int:
    return max(1, abs(x).bit_length())


def _ceil_log2_positive(x: int) -> int:
    if x < 1:
        raise ValueError("positive argument required")
    return (x - 1).bit_length()


@dataclass(frozen=True, slots=True)
class DeformationOutputHeight:
    """Bit upper bounds for every *final* coefficient of H(center+z).

    Bounds are inclusive: reduced numerators and denominators have at most
    the reported number of bits. They do not apply to intermediate values.
    """

    variables: int
    clauses: int
    occurrences: int
    rational_coefficient_count: int
    polynomial_degree: int
    maximum_input_component_bits: int
    output_degree_upper: int
    numerator_bits_upper: int
    denominator_bits_upper: int
    common_denominator_bits_upper: int

    def covers(self, coefficient: Fraction) -> bool:
        """Check a completed exact result; never used to evaluate H."""
        return (
            _bits(coefficient.numerator) <= self.numerator_bits_upper
            and _bits(coefficient.denominator) <= self.denominator_bits_upper
        )


def universal_deformation_output_height(
    formula: CNFFormula,
    replacements: ReplacementSystem,
    center: Rational,
) -> DeformationOutputHeight:
    """Calculate a polynomial-size universal OUTPUT certificate.

    The replacement system is independently validated against the CNF,
    but no evaluation or enumeration is performed. Arbitrarily large
    rational inputs remain represented symbolically by their bit lengths.
    """
    replacements.validate(formula)
    t = _exact_fraction(center)
    n, m = formula.nvars, len(formula.clauses)
    occurrences = sum(map(len, formula.clauses))
    coefficient_count = 0
    max_degree = 0
    bits = max(_bits(t.numerator), _bits(t.denominator))
    for row in replacements.clauses:
        for form in row:
            for poly in form.coefficients:
                coefficient_count += len(poly.coefficients)
                max_degree = max(max_degree, poly.degree)
                for value in poly.coefficients:
                    bits = max(bits, _bits(value.numerator), _bits(value.denominator))

    # Each occurrence stores exactly n polynomials and each canonical
    # dense polynomial has at most d+1 coefficients. Thus K itself is
    # polynomial in n, ell and d for the explicitly represented system.
    # This says nothing about the cost of constructing an implicit
    # spectral replacement or the bit length b of its rational entries.
    if coefficient_count > n * occurrences * (max_degree + 1):
        raise AssertionError("replacement coefficient representation invariant")
    common_bits_exponent = bits * (coefficient_count + max_degree)
    selection_overhead = (
        max_degree
        + _ceil_log2_positive(n * (max_degree + 1) + 1)
        + _ceil_log2_positive(max_degree + 1)
    )
    numerator = (
        n + m + occurrences * (common_bits_exponent + selection_overhead) + 1
    )
    denominator = occurrences * common_bits_exponent + 1
    return DeformationOutputHeight(
        variables=n,
        clauses=m,
        occurrences=occurrences,
        rational_coefficient_count=coefficient_count,
        polynomial_degree=max_degree,
        maximum_input_component_bits=bits,
        output_degree_upper=occurrences * max_degree,
        numerator_bits_upper=numerator,
        denominator_bits_upper=denominator,
        common_denominator_bits_upper=denominator,
    )
