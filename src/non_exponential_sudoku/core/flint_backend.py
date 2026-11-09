"""Opt-in FLINT multiplication over the existing composite-modulus Padic ring.

The default solver never imports or requires FLINT. A caller may select the
external backend for a scoped execution with ``flint_arithmetic()``. The
returned coefficient ABI remains a fixed-length tuple, not a FLINT object.

FLINT implements (Z/2**p)[U]/(f), **not** a finite field. This module owns
only the optional adapter, not the algorithm's truncation/refusal policy.
"""
from __future__ import annotations

import importlib
from collections.abc import Iterator, Sequence
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass
from functools import lru_cache
from typing import Protocol, cast


class RingSpec(Protocol):
    @property
    def e(self) -> int: ...

    @property
    def f(self) -> int: ...

    @property
    def p(self) -> int: ...

    @property
    def mask(self) -> int: ...


class _ModPolynomial(Protocol):
    def __getitem__(self, index: int) -> int: ...
    def __add__(self, other: _ModPolynomial) -> _ModPolynomial: ...
    def __sub__(self, other: _ModPolynomial) -> _ModPolynomial: ...
    def mul_mod(self, other: _ModPolynomial, modulus: _ModPolynomial) -> _ModPolynomial: ...


class _PolynomialContext(Protocol):
    def __call__(self, coefficients: Sequence[int]) -> _ModPolynomial: ...


class _FlintModule(Protocol):
    def fmpz_mod_poly_ctx(self, modulus: int) -> _PolynomialContext: ...


_ACTIVE: ContextVar[bool] = ContextVar("sudoku_flint_arithmetic", default=False)


def flint_enabled() -> bool:
    """Whether the caller explicitly selected FLINT for this execution context."""
    return _ACTIVE.get()


@contextmanager
def flint_arithmetic() -> Iterator[None]:
    """Use the exact FLINT multiplication backend inside this scope only.

    Missing FLINT is an error, not a silent fallback; nested scopes restore
    their caller's selection, including across independent async contexts.
    """
    _load_flint()  # Fail before running any arithmetic in the scope.
    token = _ACTIVE.set(True)
    try:
        yield
    finally:
        _ACTIVE.reset(token)


def _load_flint() -> _FlintModule:
    try:
        return cast(_FlintModule, importlib.import_module("flint"))
    except ImportError as exc:
        raise RuntimeError("FLINT arithmetic requires optional python-flint") from exc


class FlintRingArithmetic:
    """Tuple-compatible FLINT operations for a validated Padic ring specification."""

    def __init__(self, ring: RingSpec) -> None:
        self.e = ring.e
        self.mask = ring.mask
        self.ctx = _load_flint().fmpz_mod_poly_ctx(1 << ring.p)
        self.modulus = self.ctx([(ring.f >> i) & 1 for i in range(ring.e + 1)])

    def _poly(self, coords: Sequence[int]) -> _ModPolynomial:
        if len(coords) != self.e:
            raise ValueError("Coefficient length mismatch")
        return self.ctx([value & self.mask for value in coords])

    def _coords(self, poly: _ModPolynomial) -> tuple[int, ...]:
        return tuple(int(poly[i]) for i in range(self.e))

    def add(self, a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
        return self._coords(self._poly(a) + self._poly(b))

    def sub(self, a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
        return self._coords(self._poly(a) - self._poly(b))

    def mul(self, a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
        return self._coords(self._poly(a).mul_mod(self._poly(b), self.modulus))

    def pow(self, a: Sequence[int], power: int) -> tuple[int, ...]:
        if power < 0:
            raise ValueError("Negative powers are not supported by this adapter")
        result = self.ctx([1])
        base = self._poly(a)
        while power:
            if power & 1:
                result = result.mul_mod(base, self.modulus)
            power >>= 1
            if power:
                base = base.mul_mod(base, self.modulus)
        return self._coords(result)


@dataclass(frozen=True)
class _RingParameters:
    e: int
    f: int
    p: int

    @property
    def mask(self) -> int:
        return (1 << self.p) - 1


@lru_cache(maxsize=32)
def _cached_ring(e: int, f: int, p: int) -> FlintRingArithmetic:
    # Padic validates f, e and p before this is reached.
    return FlintRingArithmetic(_RingParameters(e, f, p))


def flint_mul(ring: RingSpec, a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
    """Reuse the FLINT polynomial modulus/context for repeated multiplications."""
    return _cached_ring(ring.e, ring.f, ring.p).mul(a, b)
