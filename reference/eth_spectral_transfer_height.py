"""Integer-only conditional height ceilings for source spectral transfer.

This is the transfer-coefficient part of the source proof obligation,
not an unconditional constructor or a projector-Gram row-norm proof.
The virtual input supplies ceil(log2(M+1)), without allocating n or D.
"""
from __future__ import annotations

from dataclasses import dataclass


def ceil_log2(value: int) -> int:
    if type(value) is not int or value < 1:
        raise ValueError("positive integer required")
    return (value - 1).bit_length()


@dataclass(frozen=True, slots=True)
class SpectralTransferHeightBudget:
    r: int
    Q: int
    R: int
    incidence_log2_upper: int
    interpolation_and_walsh_bits_upper: int
    kernel_fraction_bits_upper: int
    transferred_polynomial_fraction_bits_upper: int
    centered_occurrence_fraction_bits_upper: int
    centers: int
    selector_dimension_log2_upper: int


def spectral_transfer_height_budget(
    *, r: int, Q: int, R: int, incidence_log2_upper: int,
) -> SpectralTransferHeightBudget:
    """Upper-bound both rational numerator and denominator bit lengths.

    Let M be the number of literal incidences; the caller certifies
    ceil(log2(M+1)) <= incidence_log2_upper. The interpolation polynomial
    f has Newton coefficients (-2)**k on R consecutive integer points
    inside [0,Q]. For any integer 0<=j<=Q, f(j) is an INTEGER and
    |f(j)|<=R*(2Q)**R. The Walsh fractions have denominator 2**Q
    and at most 2**Q weighted forward differences. The kernel sums
    at most 2**Q Walsh fractions, all with the same denominator.

    Each row_at polynomial uses <=R-1 distinct factors (1-T/t),
    with 1<=t<=Q, hence its denominator divides 2**Q * Q!.
    A transferred polynomial sums at most M such terms and keeps the
    same common denominator. Center evaluation at s+1<=Q is Horner
    evaluation of degree <=R-1. No n, D or Q! is instantiated.
    """
    if any(type(v) is not int for v in (r, Q, R, incidence_log2_upper)):
        raise ValueError("exact integer parameters required")
    if r < 2 or Q < 1 or not 1 <= R <= Q + 1 or incidence_log2_upper < 0:
        raise ValueError("invalid spectral transfer parameters")

    q_bits = ceil_log2(Q + 1)
    r_bits = ceil_log2(R + 1)
    evaluation_bits = 8 + r_bits + R * ceil_log2(2 * Q + 1)
    walsh_bits = evaluation_bits + Q + R + 4
    kernel_bits = walsh_bits + Q + 4
    factorial_bits = Q * q_bits  # log2(Q!) <= Q*ceil(log2(Q+1))
    transfer_bits = kernel_bits + R + factorial_bits + incidence_log2_upper + 8
    centered_bits = transfer_bits + R * q_bits + r_bits + 8
    return SpectralTransferHeightBudget(
        r, Q, R, incidence_log2_upper,
        interpolation_and_walsh_bits_upper=walsh_bits,
        kernel_fraction_bits_upper=kernel_bits,
        transferred_polynomial_fraction_bits_upper=transfer_bits,
        centered_occurrence_fraction_bits_upper=centered_bits,
        centers=Q,
        selector_dimension_log2_upper=2 * Q * ceil_log2(r),
    )
