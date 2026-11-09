"""Closed-form integer parity-lift coefficients from the ETH manuscript.

For h(Y)=Y(Y-1), the parity polynomial has the exact decomposition

    p_ell(Y) = (1-Y) + sum_{j=1}^{ell-1}
               (-1)**j * binom(2*j,j)/2 * (1-2Y) * h(Y)**j.

The coefficient formula replaces repeated monic division and has O(ell)
rather than only the paper's conservative O(ell**2) bit height bound.
This module is a reference building block, NOT a complete general-CNF
implementation of the paper's parity-lift algorithm.
"""
from __future__ import annotations

from math import comb


def parity_lift_linear_coefficients(ell: int) -> tuple[tuple[int, int], ...]:
    """Return (constant, linear) integer coefficients of e_j(Y), j < ell."""
    if type(ell) is not int or ell < 1:
        raise ValueError('ell must be a positive integer')
    result = [(1, -1)]
    for j in range(1, ell):
        coefficient = (-1 if j % 2 else 1) * (comb(2 * j, j) // 2)
        result.append((coefficient, -2 * coefficient))
    return tuple(result)
