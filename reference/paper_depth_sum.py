"""Depth-sensitive SUPPORT bound for the literal paper schedule.

This is a conditional combinatorial estimate, not a solver bit-time bound.
The source's child-shrinkage and packet-count/precision hypotheses are
premises, and no code here proves that an input is admitted or finishes.

The previous argument took the maximum support exponent at all depths and
multiplied by their count. Tracking the geometric edge reduction instead
removes that unnecessary loglog(s) factor, yielding O(s/sqrt(log s)) for
the sum of support exponents along a paper-recursion path.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt


PAPER_COORDINATE_DIVISOR = 131072
SHRINKAGE = Fraction(3, 32)
# A generous constant proved by splitting the two geometric terms in
# sum_d sqrt(K_d*p_d)/s. It is independent of lambda and input size.
ROOT_SUM_SQRT_RATIO_CONSTANT = 256


@dataclass(frozen=True, slots=True)
class DepthRatio:
    depth: int
    active_coordinates: int
    accumulated_slot_exponent: int
    # An upper bound on K_(d,i) * p_(d,i) / s**2 for any eligible center i.
    # For enormous lambda, the 2**(-u) term may be enlarged to avoid an
    # astronomical denominator; enlargement preserves the inequality.
    color_precision_ratio_ceiling: Fraction


def paper_depth_ratios(lambda_bits: int) -> tuple[DepthRatio, ...]:
    """Exact rational depth envelopes, allocation-free in the input scale s.

    Assumptions: M0<=s, p0<=s, paper packet-count bound, and recursive
    M_(d+1)<=(3/32)*M_d.  No network, polynomial, or tensor is allocated.
    """
    if type(lambda_bits) is not int or lambda_bits < 1:
        raise ValueError('lambda_bits must be a positive integer')
    a = 0
    rho = Fraction(1)
    d = 0
    result: list[DepthRatio] = []
    while (u := lambda_bits // (PAPER_COORDINATE_DIVISOR * (1 << d))) > 0:
        a += 2 * u
        # A bounded denominator makes the certificate safe for lambda with
        # millions of bits. The omitted 2**(-u) is even smaller.
        capped_u = min(u, 2 * lambda_bits.bit_length())
        ratio = (3 * rho * (37 + 8 * (a + 1)) / (1 << capped_u)
                 + 192 * rho * rho / u)
        result.append(DepthRatio(d, u, a, ratio))
        rho *= SHRINKAGE
        d += 1
    return tuple(result)


@dataclass(frozen=True, slots=True)
class SummedPaperSupport:
    """A sufficient symbolic upper bound on SUM of local support exponents.

    This bounds sum_d 4*ceil(sqrt(K_d*p_d)), not the full solver's runtime.
    If no paper level is active, the sum is zero.
    """
    input_scale: int
    lambda_bits: int
    first_active_coordinates: int
    active_depths: int
    log2_support_exponent_sum_ceiling: int


def summed_paper_support_exponent(s: int) -> SummedPaperSupport:
    """Compute an integer ceiling O(s/sqrt(lambda)) without enumerating states.

    Put U=floor(lambda/131072)>=1. The appendix-style estimates imply
    sum_d sqrt(K_d*p_d)/s < 256/sqrt(U). Each ceil contributes at most 1.
    Using floor(sqrt(U)) in the denominator only enlarges the bound.
    """
    if type(s) is not int or s < 2:
        raise ValueError('s must be an integer >= 2')
    lam = (s - 1).bit_length()
    U = lam // PAPER_COORDINATE_DIVISOR
    if U < 1:
        return SummedPaperSupport(s, lam, 0, 0, 0)
    D = U.bit_length()  # d=0,...,floor(log2 U)
    root = max(1, isqrt(U))
    scale_ceiling = (s + root - 1) // root
    return SummedPaperSupport(
        s, lam, U, D,
        4 * ROOT_SUM_SQRT_RATIO_CONSTANT * scale_ceiling + 4 * D,
    )
