"""Narrow optional exact-arithmetic adapters; no implicit backend substitution.

The in-package Fraction implementation remains the independently executable
reference. FLINT is selected explicitly and is never emulated when missing.
Only public results are converted back to canonical Fractions. Intermediate
FLINT objects remain native, while Python reference models stay independent.
"""
from __future__ import annotations

from dataclasses import dataclass
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
    """Exact numeric export, without a decimal or textual round trip."""
    return Fraction(int(value.numerator), int(value.denominator))


def _poly(coefficients: tuple[Fraction, ...], flint: Any) -> Any:
    return flint.fmpq_poly([_q(value, flint) for value in coefficients])


def _coefficients(poly: Any) -> tuple[Fraction, ...]:
    values = tuple(_from_flint(value) for value in poly.coeffs())
    return values if values else (Fraction(0),)


@dataclass(frozen=True, slots=True)
class _NativePoly:
    """Private FLINT rational polynomial, exported only at an API boundary.

    Keeping this wrapper small lets algorithms share their native operations
    while their independent Python reference representations stay unchanged.
    No FLINT import occurs merely from importing this module.
    """

    value: Any

    @classmethod
    def from_coefficients(cls, coefficients: tuple[Fraction, ...], flint: Any) -> _NativePoly:
        return cls(_poly(coefficients, flint))

    @property
    def degree(self) -> int:
        return max(0, len(self.value) - 1)

    @property
    def length(self) -> int:
        return max(1, len(self.value))

    def export(self) -> tuple[Fraction, ...]:
        return _coefficients(self.value)

    def __add__(self, other: _NativePoly) -> _NativePoly:
        return _NativePoly(self.value + other.value)

    def __sub__(self, other: _NativePoly) -> _NativePoly:
        return _NativePoly(self.value - other.value)

    def __neg__(self) -> _NativePoly:
        return _NativePoly(-self.value)

    def __mul__(self, other: _NativePoly) -> _NativePoly:
        return _NativePoly(self.value * other.value)

    def truncate(self, length: int) -> _NativePoly:
        return _NativePoly(self.value.truncate(length))


def _native_bits(poly: _NativePoly) -> tuple[int, ...]:
    """Inspect native numerators and denominators without Fraction exports."""
    return tuple(max(c.numerator.bit_length(), c.denominator.bit_length())
                 for c in poly.value.coeffs())


def flint_polynomial_op(
    op: Literal['add', 'sub', 'mul'],
    left: tuple[Fraction, ...], right: tuple[Fraction, ...],
    *, max_length: int | None = None,
) -> tuple[Fraction, ...]:
    """Exact FLINT polynomial operation, optionally truncated to length."""
    if max_length is not None and (type(max_length) is not int or max_length < 1):
        raise ValueError('max_length must be a positive integer')
    flint = require_flint()
    a = _poly(left, flint)
    b = _poly(right, flint)
    if op == 'add':
        result = a + b
    elif op == 'sub':
        result = a - b
    elif op == 'mul':
        result = (a.mul_low(b, max_length) if max_length is not None and hasattr(a, 'mul_low')
                  else a * b)
    else:
        raise ValueError('unknown FLINT polynomial operation')
    if max_length is not None:
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
