"""Exact, allocation-free audit of the October 25 main-body ETH parameters.

The main-body theorem uses lambda=ceil(log2 n), nu=ceil(log2 lambda),
 r=floor(sqrt(lambda)/nu**2), Q=floor(lambda/(128*nu)),
 R=4*ceil(sqrt(lambda)), tau=1/(r*lambda), D=r**(2*Q).

This module checks the *stated sufficient inequalities*, not empirical
performance. In particular, a successful small spectral construction does not
constitute a successful paper-parameter construction. No exponential search
or solver fallback is performed here.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt

from non_exponential_sudoku.runtime.budget import CapacityError

from .cnf import CNFFormula


def _ceil_root(value: int) -> int:
    root = isqrt(value)
    return root if root * root == value else root + 1


@dataclass(frozen=True, slots=True)
class PaperParameters:
    """Literal integer parameters in the revised manuscript's Step 5.

    Undefined small-n regimes may have zero or unusable r/Q; then D=0,
    tau=None and q=J=None. Values are never replaced by toy parameters.
    """

    n: int
    lambda_bits: int
    nu_bits: int
    r: int
    Q: int
    R: int
    tau: Fraction | None
    D: int
    q: int | None
    J: int | None
    interval_start: int | None
    interval_end: int | None

    @property
    def defined(self) -> bool:
        return self.r >= 2 and self.Q >= 1 and self.interval_start is not None


def derive_paper_parameters(n: int, *, max_integer_bits: int = 1_000_000) -> PaperParameters:
    """Compute all manuscript constants exactly using integer arithmetic.

    n may represent a hypothetical dimension; no formula or n-element array
    is ever allocated. The integer-size cap is explicit and checked *before*
    exponentiation, preventing a pathological input from exhausting memory.
    """
    if type(n) is not int or n < 0:
        raise ValueError('n must be a nonnegative integer')
    if type(max_integer_bits) is not int or max_integer_bits < 1:
        raise ValueError('max_integer_bits must be a positive integer')
    lam = (n - 1).bit_length()
    nu = (lam - 1).bit_length() if lam > 0 else 0
    if nu == 0:
        return PaperParameters(n, lam, nu, 0, 0, 4 * _ceil_root(lam), None,
                               0, None, None, None, None)
    r = isqrt(lam) // (nu * nu)
    Q = lam // (128 * nu)
    R = 4 * _ceil_root(lam)
    if r < 2 or Q < 1:
        return PaperParameters(n, lam, nu, r, Q, R, None,
                               0, None, None, None, None)
    # Upper bound for bit length of D = r**(2Q). Avoid constructing huge D.
    if 2 * Q * r.bit_length() > max_integer_bits:
        raise CapacityError('ETH paper parameter integer-size limit')
    D = r ** (2 * Q)
    tau = Fraction(1, r * lam)
    q = (3 * n * R) // Q
    # A0 = floor(Q*(r-1)/(2r) - (R-1)/2), derived with integer division.
    a0 = (Q * (r - 1) - r * (R - 1)) // (2 * r)
    return PaperParameters(n, lam, nu, r, Q, R, tau, D, q, q + 1, a0, a0 + R - 1)


@dataclass(frozen=True, slots=True)
class PaperAdmission:
    """Statement-level premises, with every failed condition exposed."""

    parameters: PaperParameters
    M: int
    max_variable_occurrences: int
    max_clause_width: int
    conditions: tuple[tuple[str, bool], ...]

    @property
    def admitted(self) -> bool:
        return all(passed for _, passed in self.conditions)

    @property
    def failures(self) -> tuple[str, ...]:
        return tuple(label for label, passed in self.conditions if not passed)

    def require(self) -> None:
        """Fail closed rather than using an unproved demo schedule."""
        if not self.admitted:
            raise PaperParametersUnavailable('paper parameter prerequisites not met: '
                                             + ', '.join(self.failures))


class PaperParametersUnavailable(ValueError):
    """The explicit manuscript parameter theorem cannot be invoked."""


def audit_paper_bounds(
    n: int, M: int, *, b: int, w: int,
    max_integer_bits: int = 1_000_000,
) -> PaperAdmission:
    """Audit numeric hypotheses without instantiating n variables.

    `b` is maximal variable occurrences and `w` is maximal factor width.
    This is for the bounded-width/occurrence main-body theorem, not general
    CNF; general CNF still needs count-preserving disjoint sparsification.

    The tail test R**2 >= 2048*Q*nu is the *sufficient* bound actually
    verified in Step 5. It is intentionally not replaced by an inaccurate
    floating-point evaluation of exp(-R**2/(8Q)).
    """
    if any(type(v) is not int or v < 0 for v in (M, b, w)):
        raise ValueError('M, b and w must be nonnegative integers')
    p = derive_paper_parameters(n, max_integer_bits=max_integer_bits)
    defined = p.defined
    # Short circuits avoid materializing enormous powers when the parameters
    # have not reached the required domain.
    checks = (
        ('n_positive', n > 0),
        ('three_occurrences_and_width_three', b <= 3 and w <= 3),
        ('incidence_range', n <= M <= 3 * n),
        ('nonempty_factors', M > 0 and b > 0 and w > 0),
        ('r_at_least_two', p.r >= 2),
        ('Q_at_least_one', p.Q >= 1),
        ('R_at_least_32', p.R >= 32),
        ('six_R_at_most_Q', p.Q >= 6 * p.R),
        ('spectral_interval_inside_0_to_Q', defined and p.interval_start is not None
         and p.interval_start >= 0 and p.interval_end is not None and p.interval_end <= p.Q),
        ('balancing_incidence_inequality', defined and 2 * (b + w) * p.D * p.D <= M),
        ('balancing_groups_inequality', defined and 2 * p.Q * p.r * p.r <= n),
        ('spectral_tail_sufficient_inequality', defined and p.R * p.R >=
         2048 * p.Q * p.nu_bits),
        ('dimension_at_most_2n_power_1_over_128', defined and p.D ** 128 <= 2 * n),
        ('taylor_order_at_most_half_n', defined and p.q is not None and 2 * p.q <= n),
        ('hermite_unique_degree_3nR', defined and p.J is not None and
         p.Q * p.J > 3 * n * p.R),
    )
    return PaperAdmission(p, M, b, w, checks)


def audit_bounded_cnf(formula: CNFFormula) -> PaperAdmission:
    """Inspect the actual canonical CNF and audit its literal incidences."""
    occurrences = [0] * formula.nvars
    for clause in formula.clauses:
        for lit in clause:
            occurrences[abs(lit) - 1] += 1
    return audit_paper_bounds(
        formula.nvars,
        sum(len(clause) for clause in formula.clauses),
        b=max(occurrences, default=0),
        w=max(map(len, formula.clauses), default=0),
    )
