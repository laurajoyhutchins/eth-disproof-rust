"""Exact tapered Hermite recovery through one coefficient formula.

Both eager and streaming callers use :class:`StreamingHermite`. Keeping the
rational accumulation in one place prevents a silent divergence between the
interpolation and Taylor-jet branches.
"""
from __future__ import annotations

from collections.abc import Mapping, Sequence
from typing import cast

from ..core.algebra import Padic, RingCoords
from ..core.jets import JetRing
from ..core.lazy_coefficients import NestedCoords
from .streaming import StreamingHermite


def tapered_recover(
    jets: Mapping[int, Sequence[RingCoords]],
    M: int,
    L: int,
    u: int,
    base_p: int,
    e: int,
    f: int,
) -> RingCoords:
    """Recover the constant coefficient from ordinary 2-adic center jets."""
    return cast(RingCoords, tapered_recover_over_ring(
        jets, M, L, u, Padic(e, f, base_p),
    ))


def tapered_recover_over_ring(
    jets: Mapping[int, Sequence[NestedCoords]],
    M: int,
    L: int,
    u: int,
    outer_ring: Padic | JetRing,
) -> NestedCoords:
    """Recover ordinary or nested coefficients from exact stored centers.

    Eager callers retain the center jets; the accumulator itself consumes
    each center without retaining its coefficients. Both execution schedules
    use precisely the same rational Hermite formula.
    """
    accumulator = StreamingHermite(M, L, u, outer_ring)
    for center, coefficients in jets.items():
        accumulator.add_center(center, coefficients)
    return accumulator.finish()
