"""Source origin Hermite CRT: polynomial-bit intermediate bound contracts."""
from __future__ import annotations

from fractions import Fraction
from math import comb
from random import Random

import pytest

from non_exponential_sudoku.eth.interpolation import (
    HermiteDatum, HermiteLimits, interpolate_origin_hermite,
)
from non_exponential_sudoku.eth.polynomial import Polynomial
from reference.eth_hermite_origin_budget import hermite_origin_budget


def _bits(value: Fraction) -> int:
    return max(1, abs(value.numerator).bit_length(), value.denominator.bit_length())


def _traced_origin(data: tuple[HermiteDatum, ...]) -> tuple[Fraction, int, int]:
    """Independent, source-shaped CRT with EVERY scalar arithmetic result observed."""
    bits, operations = 1, 0

    def observe(value: Fraction) -> Fraction:
        nonlocal bits, operations
        bits = max(bits, _bits(value))
        operations += 1
        return value

    def truncated_product(
        left: tuple[Fraction, ...], right: tuple[Fraction, ...], order: int,
    ) -> tuple[Fraction, ...]:
        output = [Fraction(0)] * order
        for i, a in enumerate(left[:order]):
            if not a:
                continue
            for j, b in enumerate(right[:order - i]):
                if b:
                    output[i + j] = observe(
                        output[i + j] + observe(a * b)
                    )
        return tuple(output)

    total = Fraction(0)
    for i, datum in enumerate(data):
        J = len(datum.coefficients)
        modulus = (Fraction(1),)
        modulus_zero = Fraction(1)
        for j, other in enumerate(data):
            if i == j:
                continue
            m = len(other.coefficients)
            gap = datum.center - other.center
            modulus_zero = observe(
                modulus_zero * observe((-other.center) ** m)
            )
            factor = tuple(
                observe(Fraction(comb(m, k)) * observe(gap ** (m - k)))
                for k in range(min(m, J - 1) + 1)
            )
            modulus = truncated_product(modulus, factor, J)
        modulus += (Fraction(0),) * (J - len(modulus))
        inv = [observe(1 / modulus[0])]
        for k in range(1, J):
            residual = Fraction(0)
            for j in range(1, k + 1):
                residual = observe(
                    residual + observe(modulus[j] * inv[k - j])
                )
            inv.append(observe(-residual / modulus[0]))
        quotient = truncated_product(datum.coefficients, tuple(inv), J)
        value = Fraction(0)
        for coefficient in reversed(quotient):
            value = observe(
                observe(value * -datum.center) + coefficient
            )
        total = observe(
            total + observe(modulus_zero * value)
        )
    return total, bits, operations


@pytest.mark.checkpoint
def test_200_seeded_exact_hermite_origin_traces_fit_intermediate_bit_envelope() -> None:
    rng = Random(459020)
    for _ in range(200):
        centers = tuple(rng.sample((-5, -3, -2, -1, 1, 2, 3, 5), rng.randint(1, 4)))
        orders = tuple(rng.randint(1, 4) for _ in centers)
        N = sum(orders)
        poly = Polynomial(tuple(
            Fraction(rng.randint(-100, 100), rng.randint(1, 20))
            for _ in range(N)
        ))
        data = tuple(
            HermiteDatum(Fraction(c), poly.taylor(c, order - 1).coefficients
                         + (Fraction(0),) * max(
                             0, order - len(poly.taylor(c, order - 1).coefficients)))
            for c, order in zip(centers, orders)
        )
        input_bits = max(
            _bits(value) for datum in data for value in datum.coefficients
        )
        budget = hermite_origin_budget(
            centers, orders, input_fraction_bits=input_bits,
        )
        traced, max_bits, operations = _traced_origin(data)
        actual = interpolate_origin_hermite(
            data, degree_bound=N - 1,
            limits=HermiteLimits(
                max_degree=max(256, N), max_conditions=max(512, N),
                max_operations=5_000_000, max_coefficient_bits=200_000,
            ),
        )
        assert traced == actual.value == poly.at_zero
        assert max_bits <= budget.intermediate_fraction_bits_upper
        assert operations <= budget.rational_operations_upper
        assert actual.stats.max_coefficient_bits <= (
            budget.intermediate_fraction_bits_upper
        )


@pytest.mark.checkpoint
def test_hermite_budget_fails_closed_on_nonintegral_and_repeated_centers() -> None:
    for centers, orders in (
        ((1, 1), (2, 2)),
        ((0, 2), (2, 2)),
        ((Fraction(1, 2), 2), (2, 2)),
        ((1,), (0,)),
        ((), ()),
        ((1, 2), (1,)),
    ):
        with pytest.raises(ValueError):
            hermite_origin_budget(centers, orders, input_fraction_bits=10)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        hermite_origin_budget((1, 2), (2, 2), input_fraction_bits=0)
