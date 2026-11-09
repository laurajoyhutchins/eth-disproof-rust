"""Independent exact SymPy oracle for the solver's unramified 2-adic ring.

SymPy is used over ZZ, followed by a monic polynomial remainder and reduction
modulo 2**p. Do not use SymPy's GF(2**p) or GF(p) domains for this ring:
Z/(2**p)[U]/(f) is not a field when p > 1.

This module is never imported by the production package.
"""
from __future__ import annotations

from collections.abc import Sequence
from sympy import Poly, Symbol, ZZ

from non_exponential_sudoku.core.algebra import Padic


class SympyRingOracle:
    """Deliberately conversion-inclusive reference with no custom convolution."""

    def __init__(self, ring: Padic) -> None:
        self.ring = ring
        self.x = Symbol("u")  # type: ignore[no-untyped-call]
        self.modulus: Poly = Poly.from_list(
            [(ring.f >> i) & 1 for i in range(ring.e, -1, -1)],
            gens=self.x, domain=ZZ,
        )  # type: ignore[no-untyped-call]

    def poly(self, coords: Sequence[int]) -> Poly:
        if len(coords) != self.ring.e:
            raise ValueError("Coefficient length mismatch")
        return Poly.from_list(list(reversed(coords)), gens=self.x, domain=ZZ)  # type: ignore[no-untyped-call,no-any-return]

    def coords(self, poly: Poly) -> tuple[int, ...]:
        remainder = poly.rem(self.modulus)  # type: ignore[no-untyped-call]
        coefficients = [int(v) % (1 << self.ring.p)
                        for v in reversed(remainder.all_coeffs())] if not remainder.is_zero else []
        return tuple((coefficients + [0] * self.ring.e)[:self.ring.e])

    def add(self, a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
        return self.coords(self.poly(a) + self.poly(b))

    def sub(self, a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
        return self.coords(self.poly(a) - self.poly(b))

    def mul(self, a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
        return self.coords(self.poly(a) * self.poly(b))

    def pow(self, a: Sequence[int], n: int) -> tuple[int, ...]:
        if n < 0:
            raise ValueError("Only nonnegative oracle exponents are supported")
        return self.coords(self.poly(a) ** n)


def irreducible_mod_two(poly: int, degree: int) -> bool:
    """SymPy's independent GF(2) irreducibility check."""
    if degree < 1 or poly.bit_length() != degree + 1:
        return False
    x = Symbol("u")  # type: ignore[no-untyped-call]
    return bool(Poly.from_list([(poly >> i) & 1 for i in range(degree, -1, -1)],
                               gens=x, modulus=2).is_irreducible)  # type: ignore[no-untyped-call]
