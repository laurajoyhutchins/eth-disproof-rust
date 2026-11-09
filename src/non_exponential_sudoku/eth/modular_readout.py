"""Exact small-modulus Hermite origin reconstruction and bounded CRT.

This modular implementation optimizes the readout only.  Supplying rational
Taylor data means coefficient growth in the upstream Taylor computation has
NOT been removed.  CRT recovers the true integer origin only when the caller
has a mathematically established inclusive bound on that integer; this is
not a shortcut for the October 25 paper's unreduced parity-lift readout.
"""
from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction

from non_exponential_sudoku.runtime.budget import CapacityError

from .interpolation import HermiteDatum


def _residue(value: Fraction, modulus: int) -> int:
    try:
        inverse = pow(value.denominator % modulus, -1, modulus)
    except ValueError as exc:
        raise ValueError('rational denominator is not invertible modulo modulus') from exc
    return (value.numerator % modulus) * inverse % modulus


def interpolate_origin_mod(
    data: Sequence[HermiteDatum], *, modulus: int,
) -> int:
    """Read the unique Hermite interpolant at zero in Z/modulus.

    All rational denominators and local Hermite moduli must be units.
    For composite moduli this remains valid when those inverses exist.
    """
    if type(modulus) is not int or modulus <= 1:
        raise ValueError('modulus must be an integer greater than one')
    if not data:
        raise ValueError('Hermite origin needs at least one center')
    if any(not isinstance(datum, HermiteDatum) for datum in data):
        raise TypeError('modular Hermite requires HermiteDatum inputs')
    centers = [_residue(datum.center, modulus) for datum in data]
    if len(set(centers)) != len(centers):
        raise ValueError('Hermite centers collide modulo modulus')

    def multiply_low(
        left: Sequence[int], right: Sequence[int], order: int,
    ) -> list[int]:
        result = [0] * order
        for i, a in enumerate(left):
            if i >= order:
                break
            for j, b in enumerate(right):
                if i + j >= order:
                    break
                result[i + j] = (result[i + j] + a * b) % modulus
        return result

    value = 0
    for index, datum in enumerate(data):
        center = centers[index]
        order = len(datum.coefficients)
        local_modulus: list[int] = [1]
        modulus_at_zero = 1
        for j, other in enumerate(data):
            if index == j:
                continue
            power = len(other.coefficients)
            modulus_at_zero = modulus_at_zero * pow(-centers[j], power, modulus) % modulus
            gap = (center - centers[j]) % modulus
            factor = [1]
            for _ in range(power):
                factor = multiply_low(factor, (gap, 1), order)
            local_modulus = multiply_low(local_modulus, factor, order)
        local_modulus.extend([0] * (order - len(local_modulus)))
        try:
            inverse_constant = pow(local_modulus[0], -1, modulus)
        except ValueError as exc:
            raise ValueError('Hermite center differences are not units modulo modulus') from exc
        inverse = [inverse_constant]
        for k in range(1, order):
            residual = sum(local_modulus[j] * inverse[k - j]
                           for j in range(1, k + 1))
            inverse.append((-residual * inverse_constant) % modulus)
        local_data = [_residue(c, modulus) for c in datum.coefficients]
        quotient = multiply_low(local_data, inverse, order)
        local_value = 0
        for coefficient in reversed(quotient):
            local_value = (local_value * -center + coefficient) % modulus
        value = (value + modulus_at_zero * local_value) % modulus
    return value


def interpolate_integer_origin_crt(
    data: Sequence[HermiteDatum], *, max_value: int,
    moduli: Sequence[int],
) -> int:
    """Recover P(0) when it is PROVEN to be an integer in [0,max_value].

    Each modulus must be coprime to the accumulated product and admit all
    needed rational inverses.  The final modulus product must exceed
    max_value.  The proof of the value bound belongs to the caller.
    """
    if type(max_value) is not int or max_value < 0:
        raise ValueError('max_value must be a nonnegative integer')
    recovered = 0
    product = 1
    for modulus in moduli:
        if product > max_value:
            break
        if type(modulus) is not int or modulus <= 1:
            raise ValueError('CRT moduli must be integers greater than one')
        try:
            product_inverse = pow(product, -1, modulus)
        except ValueError as exc:
            raise ValueError('CRT moduli must be pairwise coprime') from exc
        residue = interpolate_origin_mod(data, modulus=modulus)
        correction = ((residue - recovered) * product_inverse) % modulus
        recovered += product * correction
        product *= modulus
    if product <= max_value:
        raise CapacityError('insufficient CRT modulus product for exact integer bound')
    return recovered
