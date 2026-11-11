"""A polynomial intermediate bit-work bound for actual origin Hermite CRT.

Source correspondence: eth/interpolation.py::interpolate_origin_hermite.
Applies to DISTINCT NONZERO INTEGRAL centers (as supplied by source Step 4),
and provided exact Taylor data. Does not construct the data or bypass caps.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence


def ceil_log2(value: int) -> int:
    if type(value) is not int or value < 1:
        raise ValueError("positive integer required")
    return (value - 1).bit_length()


@dataclass(frozen=True, slots=True)
class HermiteOriginBudget:
    centers: int
    conditions: int
    maximum_abs_center: int
    input_fraction_bits: int
    intermediate_fraction_bits_upper: int
    rational_operations_upper: int
    retained_fraction_slots_upper: int


def hermite_origin_budget(
    centers: Sequence[int], multiplicities: Sequence[int], *,
    input_fraction_bits: int,
) -> HermiteOriginBudget:
    """Bound intermediates in the source's local-modulus inverse CRT.

    Put N=sum(J_i), C=max|c_i|, and T=(2C+1)**N. For each i,
       M_i(z)=product_(j!=i) (c_i-c_j+z)**J_j
    has integral coefficients of absolute magnitude <=T, and
    a_i=M_i(0) is a nonzero integer of magnitude <=T.

    The inverse-jet recurrence gives b_k=u_k/a_i**(k+1), with
    |u_k| <= (N*T**2)**k. All input Taylor denominators divide the
    product D0 of the N input denominators, log2(D0)<=N*B.
    Local quotients have denominator dividing D0*a_i**J_i.
    The sum at the origin has denominator dividing
       D0 * product_i a_i**J_i,
    whose bit length <=N*B + N**2*ceil(log2(2C+2)).
    Charge the intermediate products, prefix sums, inverse residuals,
    Horner stages and integer powers with a deliberately larger
    polynomial ceiling. This is a mathematical schoolbook model,
    not a CPython allocation count or a machine-instruction count.
    """
    if not centers or len(centers) != len(multiplicities):
        raise ValueError("nonempty matching centers and orders required")
    if (any(type(center) is not int or center == 0 for center in centers)
            or len(set(centers)) != len(centers)):
        raise ValueError("distinct nonzero integral centers required")
    if any(type(order) is not int or order < 1 for order in multiplicities):
        raise ValueError("positive integral orders required")
    if type(input_fraction_bits) is not int or input_fraction_bits < 1:
        raise ValueError("positive input bits required")
    N = sum(multiplicities)
    C = max(map(abs, centers))
    W = ceil_log2(2 * C + 2)
    bits = 32 * (N + 1) ** 2 * (
        input_fraction_bits + W + ceil_log2(N + 1) + 3
    )
    operations = 128 * (N + 1) ** 4
    slots = 16 * (N + 1) ** 2
    return HermiteOriginBudget(
        len(centers), N, C, input_fraction_bits,
        bits, operations, slots,
    )
