"""Narrow optional exact-arithmetic adapters; no implicit backend substitution.

The in-package Fraction implementation remains the independently executable
reference. FLINT is selected explicitly and is never emulated when missing.
All externally produced values are converted back into validated Fractions,
so the existing public models and capacity checks stay authoritative.
"""
from __future__ import annotations

from fractions import Fraction
from importlib import import_module
from typing import Any, Literal

ArithmeticBackend = Literal['python', 'flint']


class BackendUnavailableError(RuntimeError):
    """An explicitly requested optional backend is not installed."""


def require_flint() -> Any:
    try:
        return import_module('flint')
    except ImportError as exc:
        raise BackendUnavailableError(
            'FLINT backend requires python-flint; install with the eth-flint extra'
        ) from exc


def _q(value: Fraction, flint: Any) -> Any:
    # Construct from exact integer numerator/denominator; never pass floats.
    return flint.fmpq(value.numerator, value.denominator)


def _from_flint(value: Any) -> Fraction:
    # fmpq stringifies to a reduced decimal-free integer or a/b rational.
    return Fraction(str(value))


def _poly(coefficients: tuple[Fraction, ...], flint: Any) -> Any:
    return flint.fmpq_poly([_q(value, flint) for value in coefficients])


def _coefficients(poly: Any) -> tuple[Fraction, ...]:
    values = tuple(_from_flint(value) for value in poly.coeffs())
    return values if values else (Fraction(0),)


def flint_polynomial_op(
    op: Literal['add', 'sub', 'mul'],
    left: tuple[Fraction, ...], right: tuple[Fraction, ...],
    *, max_length: int | None = None,
) -> tuple[Fraction, ...]:
    """Exact FLINT polynomial operation, optionally truncated to length."""
    flint = require_flint()
    a = _poly(left, flint)
    b = _poly(right, flint)
    if op == 'add':
        result = a + b
    elif op == 'sub':
        result = a - b
    elif op == 'mul':
        result = a * b
    else:
        raise ValueError('unknown FLINT polynomial operation')
    if max_length is not None:
        if type(max_length) is not int or max_length < 1:
            raise ValueError('max_length must be a positive integer')
        result = result.truncate(max_length)
    return _coefficients(result)


def flint_taylor(
    coefficients: tuple[Fraction, ...], center: Fraction, order: int,
) -> tuple[Fraction, ...]:
    """Truncated Horner evaluation at T=center+z over exact Q[z]."""
    if type(order) is not int or order < 0:
        raise ValueError('Taylor order must be nonnegative')
    flint = require_flint()
    substitution = _poly((center, Fraction(1)) if order else (center,), flint)
    result = _poly((Fraction(0),), flint)
    for coefficient in reversed(coefficients):
        result = (result * substitution + _poly((coefficient,), flint)).truncate(order + 1)
    return _coefficients(result)


def flint_row_combination(
    rows: tuple[tuple[int, ...], ...], target: tuple[Fraction, ...],
) -> tuple[Fraction, ...]:
    """Witness for C^T lambda = target via FLINT's exact rational RREF.

    A free-variable-zero witness is returned and checked against *all* rows.
    No rounded or least-squares solutions are accepted.
    """
    flint = require_flint()
    width, count = len(target), len(rows)
    if any(len(row) != width for row in rows):
        raise ValueError('measurement matrix width mismatch')
    if not width or not count:
        if any(target):
            raise ValueError('cross-group vector outside measurement row space')
        return tuple(Fraction(0) for _ in rows)
    entries = [_q(Fraction(rows[j][i]), flint) for i in range(width)
               for j in range(count)]
    # Build the augmented matrix row-by-row.
    augmented = [entries[i * count:(i + 1) * count] + [_q(target[i], flint)]
                 for i in range(width)]
    matrix = flint.fmpq_mat(augmented)
    reduced, _rank = matrix.rref()
    solution = [Fraction(0) for _ in rows]
    for i in range(width):
        pivot = next((j for j in range(count) if reduced[i, j] != 0), None)
        rhs = _from_flint(reduced[i, count])
        if pivot is None:
            if rhs:
                raise ValueError('cross-group vector outside measurement row space')
            continue
        solution[pivot] = rhs
    if any(sum((solution[j] * rows[j][i] for j in range(count)), Fraction(0)) != target[i]
           for i in range(width)):
        raise ValueError('cross-group vector outside measurement row space')
    return tuple(solution)


def check_arithmetic_backend(backend: ArithmeticBackend) -> None:
    if backend == 'python':
        return
    if backend == 'flint':
        require_flint()
        return
    raise ValueError(f'unknown exact arithmetic backend: {backend!r}')
