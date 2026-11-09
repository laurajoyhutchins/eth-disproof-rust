"""Bounded finite-ring readout contracts: no implicit rational reconstruction."""
from __future__ import annotations

from fractions import Fraction

import pytest

from non_exponential_sudoku.eth.interpolation import HermiteDatum, interpolate_hermite
from non_exponential_sudoku.eth.modular_readout import (
    interpolate_integer_origin_crt, interpolate_origin_mod,
)
from non_exponential_sudoku.eth.polynomial import Polynomial
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def _data(poly: Polynomial) -> tuple[HermiteDatum, ...]:
    settings = ((Fraction(1), 2), (Fraction(2), 2), (Fraction(3), 2))
    result = []
    for center, size in settings:
        jet = poly.taylor(center, size - 1).coefficients
        result.append(HermiteDatum(center, jet + (Fraction(0),) * (size - len(jet))))
    return tuple(result)


def test_modular_origin_matches_exact_rational_and_crt_bound() -> None:
    poly = Polynomial((156_789, Fraction(7, 2), Fraction(-13, 3),
                       Fraction(17, 5), 3, Fraction(-2, 7)))
    data = _data(poly)
    assert interpolate_hermite(data, degree_bound=5).polynomial.at_zero == 156_789
    for modulus in (101, 103, 107):
        assert interpolate_origin_mod(data, modulus=modulus) == 156_789 % modulus
    assert interpolate_integer_origin_crt(
        data, max_value=1_000_000, moduli=(101, 103, 107),
    ) == 156_789


def test_large_fractional_intermediates_use_only_small_residues() -> None:
    huge = 2 ** 300
    poly = Polynomial((123_456_789, Fraction(huge, 3), Fraction(-huge, 7),
                       Fraction(huge, 11), Fraction(-huge, 13), Fraction(huge, 17)))
    data = _data(poly)
    assert interpolate_integer_origin_crt(
        data, max_value=2 ** 32, moduli=(2_147_483_647, 2_147_483_629),
    ) == 123_456_789


def test_modular_refuses_nonunits_collisions_and_insufficient_information() -> None:
    with pytest.raises(ValueError, match='denominator'):
        interpolate_origin_mod(
            [HermiteDatum(Fraction(1, 2), (1,))], modulus=2)
    with pytest.raises(ValueError, match='collide'):
        interpolate_origin_mod(
            [HermiteDatum(Fraction(1), (1,)), HermiteDatum(Fraction(3), (1,))],
            modulus=2)
    with pytest.raises(CapacityError, match='insufficient CRT'):
        interpolate_integer_origin_crt(_data(Polynomial((3,))), max_value=1_000_000,
                                       moduli=(101, 103))
    with pytest.raises(ValueError, match='coprime'):
        interpolate_integer_origin_crt(
            _data(Polynomial((3,))), max_value=1_000_000,
            moduli=(101, 101, 103))
