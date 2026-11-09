"""Streaming exact tapered Hermite recovery for recursive 2-adic contractions.

This module changes the evaluation *schedule*, not the Cauchy/mode identities,
precision formula, coefficient arithmetic, or mathematical answer.  Each
center's Taylor jet is consumed immediately and discarded.  Exact rational
accumulation is deliberately postponed until all centers have contributed:
modular reduction after each center is generally unsound because the Hermite
formula includes rational scalars with negative 2-adic valuation.

It does NOT make the current center's nested Taylor jet lazy, nor does it
implement the Cook--Mertz algorithm.  Those are distinct research questions.
"""
from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction
from math import comb
from typing import cast

from ..core.algebra import Padic, p_mul, v2
from ..core.jets import (
    JetRing, NestedRing, flatten_element, precision_ring, unflatten_element,
)
from ..core.lazy_coefficients import NestedCoords
from ..runtime.cost_ledger import charge


class StreamingHermite:
    """Exact one-center-at-a-time version of tapered_recover_over_ring.

    add_center(t, jet) accepts length q_t jets in increasing Taylor order, over
    the lifted outer coefficient ring at precisely p_t. The source jet is never
    retained. Each center may be visited once, in any order.
    """

    def __init__(self, M: int, L: int, u: int, outer_ring: Padic | JetRing) -> None:
        if M < 0 or L < 2 or L & (L - 1) or u < 1:
            raise ValueError('Invalid Hermite schedule')
        self.M, self.L, self.u, self.outer = M, L, u, outer_ring
        self.a = L.bit_length() - 1
        self.alpha = 1 << (self.a + 1)
        self.h = (3 * M + u - 1) // u
        self.qs = {t: self.h * max(0, u - v2(t))
                   for t in range(-L, L) if t != 0}
        self.dims = len(flatten_element(outer_ring.zero, outer_ring))
        self.answers = [Fraction(0) for _ in range(self.dims)]
        self.seen: set[int] = set()
        self.centers = 0
        self.max_center_coefficients = 0

    def precision(self, t: int) -> int:
        if t not in self.qs or not self.qs[t]:
            raise ValueError('Inactive or unknown center')
        return (
            self.outer.p
            + 8 * self.h * (self.L // (1 << v2(t)))
            + 8 * self.M * (self.a + 1)
        )

    def add_center(self, t: int, jet: Sequence[NestedCoords]) -> None:
        if t in self.seen:
            raise ValueError('Duplicate Hermite center')
        if t not in self.qs or self.qs[t] == 0:
            raise ValueError('Inactive Hermite center')

        order = self.qs[t]
        if len(jet) != order:
            raise ValueError(f'Center {t} needs {order} Taylor coefficients')
        ring = precision_ring(self.outer, self.precision(t))
        coefficients = cast(NestedRing, ring)

        # At T=t+alpha*z, E_t is a unit power series with constant 1:
        #   E_t(t+alpha*z) = prod_{s!=t} (1+alpha*z/(t-s))**q_s.
        # Its separate rational normalization at z=0 is
        #   E_t(0) = prod_{s!=t} (-s/(t-s))**q_s.
        unit_series = [coefficients.one]
        normalization = Fraction(1)
        for other, multiplicity in self.qs.items():
            if other == t or not multiplicity:
                continue
            normalization *= Fraction(-other, t - other) ** multiplicity
            slope = coefficients.rational(Fraction(self.alpha, t - other))
            binomial = [
                coefficients.mul(
                    coefficients.scalar(comb(multiplicity, degree)),
                    coefficients.pow(slope, degree),
                )
                for degree in range(min(multiplicity, order - 1) + 1)
            ]
            unit_series = p_mul(unit_series, binomial, coefficients, order)
        unit_series = (unit_series + [coefficients.zero] * order)[:order]

        # For E[0]=1, the reciprocal coefficients satisfy
        #   E_inv[k] = -sum_{j=1}^k E[j] * E_inv[k-j].
        reciprocal = [coefficients.one]
        for degree in range(1, order):
            convolution = coefficients.zero
            for j in range(1, degree + 1):
                convolution = coefficients.add(
                    convolution,
                    coefficients.mul(unit_series[j], reciprocal[degree - j]),
                )
            reciprocal.append(coefficients.neg(convolution))

        quotient = p_mul(jet, reciprocal, coefficients, order)
        for degree, value in enumerate(quotient):
            scale = normalization * Fraction(-t, self.alpha) ** degree
            for coordinate, coefficient in enumerate(flatten_element(value, ring)):
                self.answers[coordinate] += scale * coefficient
                charge("recovery_rational_accumulations")

        self.seen.add(t)
        self.centers += 1
        self.max_center_coefficients = max(self.max_center_coefficients, order)

    def finish(self) -> NestedCoords:
        expected = {t for t, q in self.qs.items() if q}
        if self.seen != expected:
            raise ValueError(f'Missing Hermite centers: {sorted(expected - self.seen)}')
        R0 = precision_ring(self.outer, self.outer.p)
        padic = Padic(R0.e, R0.f, R0.p)
        result = tuple(padic.rational(v)[0] for v in self.answers)
        return unflatten_element(result, R0)
