"""Exact integer parity-lift identities, including coefficient bit height."""
from __future__ import annotations

from math import comb

import pytest

from non_exponential_sudoku.eth.parity_lift import parity_lift_linear_coefficients
from non_exponential_sudoku.eth.polynomial import ONE, ZERO, Polynomial

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize("ell", range(1, 11))
def test_parity_lift_matches_independent_binomial_polynomial(ell: int) -> None:
    y = Polynomial((0, 1))
    h = Polynomial((0, -1, 1))
    actual = ZERO
    hpower = ONE
    for a, b in parity_lift_linear_coefficients(ell):
        actual = actual + Polynomial((a, b)) * hpower
        hpower = hpower * h
    prefix = ONE
    for _ in range(ell):
        prefix = prefix * Polynomial((1, -1))
    geometric = ZERO
    power = ONE
    for j in range(ell):
        geometric = geometric + power.scale(comb(ell + j - 1, j))
        power = power * y
    assert actual == prefix * geometric

    for value in range(-5, 8):
        assert actual.evaluate(value) % (1 << ell) == int(value % 2 == 0)


@pytest.mark.parametrize("ell", [1, 2, 8, 16, 32, 64, 128])
def test_parity_lift_coefficients_have_linear_bit_height(ell: int) -> None:
    coefficients = parity_lift_linear_coefficients(ell)
    assert len(coefficients) == ell
    assert max(max(abs(a).bit_length(), abs(b).bit_length())
               for a, b in coefficients) <= 2 * ell + 1


def test_parity_lift_rejects_invalid_order() -> None:
    for bad in (0, -1, 1.5, True):
        with pytest.raises(ValueError, match='positive'):
            parity_lift_linear_coefficients(bad)  # type: ignore[arg-type]
