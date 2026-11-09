"""Native Taylor arithmetic must equal independent base-ring convolution.

These cases exercise the three native multiplication branches: scalar/scalar,
scalar/extension, and extension/extension. In particular, the high-precision
cases cannot be represented with fixed-width C integer arithmetic.
"""
from __future__ import annotations

import random

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing

pytestmark = pytest.mark.checkpoint


def _reference_mul(base, a, b):
    q = len(a)
    out = []
    for degree in range(q):
        total = base.zero
        for index in range(degree + 1):
            total = base.add(total, base.mul(a[index], b[degree - index]))
        out.append(total)
    return tuple(out)


def _make_operand(rng, base, q, *, scalar, sparse):
    values = []
    for i in range(q):
        if sparse and rng.randrange(4):
            values.append(base.zero)
        elif scalar:
            values.append(base.scalar(rng.getrandbits(base.p)))
        else:
            # Force a non-scalar extension coordinate so that the branch
            # cannot pass by exclusively exercising scalar coefficients.
            coords = [rng.getrandbits(base.p) for _ in range(base.e)]
            coords[1] |= 1
            values.append(tuple(v & base.mask for v in coords))
    return tuple(values)


@pytest.mark.requires_native
@pytest.mark.parametrize('e,p,q', [(2, 3, 1), (3, 19, 4),
                                    (5, 131, 9), (8, 257, 16)])
@pytest.mark.parametrize('scalar_a,scalar_b', [(True, True), (True, False),
                                             (False, True), (False, False)])
@pytest.mark.parametrize('sparse', [False, True])
def test_exact_native_sparse_jets_match_generic_convolution(
        e, p, q, scalar_a, scalar_b, sparse):
    native = pytest.importorskip('native_ring')
    base = Padic(e, modulus_polynomial(e), p)
    ring = JetRing(base, q)
    rng = random.Random(100000 * e + 1000 * p + 100 * q
                        + 10 * scalar_a + 5 * scalar_b + sparse)
    for _ in range(3):
        a = _make_operand(rng, base, q, scalar=scalar_a, sparse=sparse)
        b = _make_operand(rng, base, q, scalar=scalar_b, sparse=sparse)
        expected = _reference_mul(base, a, b)
        assert native.jet_mul(a, b, e, base.f, base.mask) == expected
        assert ring.mul(a, b) == expected
        assert native.jet_add(a, b, base.mask) == tuple(
            base.add(x, y) for x, y in zip(a, b))
        assert native.jet_sub(a, b, base.mask) == tuple(
            base.sub(x, y) for x, y in zip(a, b))
        # Independent generic JetRing fallback, including nested use.
        ring._native_mul = None
        ring._native_add = None
        ring._native_sub = None
        assert ring.mul(a, b) == expected
        assert ring.add(a, b) == tuple(base.add(x, y) for x, y in zip(a, b))
        assert ring.sub(a, b) == tuple(base.sub(x, y) for x, y in zip(a, b))


@pytest.mark.requires_native
def test_sparse_native_truncation_and_high_extension_coefficients():
    native = pytest.importorskip('native_ring')
    base = Padic(5, modulus_polynomial(5), 173)
    q = 7
    unit_u = base.basis(2)
    leading = ((1 << 170) + 13,) + (0,) * (base.e - 1)
    a = (base.zero,) * (q - 1) + (unit_u,)
    b = (base.zero,) * (q - 1) + (leading,)
    # The only product has degree 2(q-1), which must be discarded.
    assert native.jet_mul(a, b, base.e, base.f, base.mask) == (base.zero,) * q
    # Reposition coefficients to make the product fit and require full U
    # reduction as well as exact 173-bit coordinate arithmetic.
    a = (unit_u,) + (base.zero,) * (q - 1)
    b = (unit_u,) + (base.zero,) * (q - 1)
    assert native.jet_mul(a, b, base.e, base.f, base.mask) == (
        base.mul(unit_u, unit_u),) + (base.zero,) * (q - 1)
    assert native.jet_mul(a, (leading,) + (base.zero,) * (q-1),
                          base.e, base.f, base.mask) == (
        base.mul(unit_u, leading),) + (base.zero,) * (q-1)


def test_nested_jets_use_generic_path_for_outer_convolution():
    base = Padic(4, modulus_polynomial(4), 97)
    inner = JetRing(base, 4)
    outer = JetRing(inner, 3)
    a = (inner.add(inner.one, inner.variable), inner.variable, inner.zero)
    b = (inner.variable, inner.one, inner.zero)
    expected = (
        inner.mul(a[0], b[0]),
        inner.add(inner.mul(a[0], b[1]), inner.mul(a[1], b[0])),
        inner.mul(a[1], b[1]),
    )
    assert outer.mul(a, b) == expected


@pytest.mark.requires_native
def test_raw_noncanonical_coordinate_representatives_are_reduced_exactly():
    """Zero/one shortcuts must normalize just like ordinary Padic arithmetic."""
    from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
    from non_exponential_sudoku.core.jets import JetRing
    native_ring = pytest.importorskip('native_ring')
    base=Padic(3,modulus_polynomial(3),7)
    ring=JetRing(base,3)
    a=((1<<200,-3,129),(-10,3,4),(0,0,0))
    b=((0,0,0),(1,0,0),(0,0,0))
    for y in (ring.zero,ring.one,b):
        assert ring.add(a,y)==tuple(base.add(x,z) for x,z in zip(a,y))
        assert ring.sub(a,y)==tuple(base.sub(x,z) for x,z in zip(a,y))
        expected=tuple(
            _exact_degree_sum(base,a,y,k) for k in range(3))
        assert ring.mul(a,y)==expected
        assert native_ring.jet_add(a,y,base.mask)==tuple(base.add(x,z) for x,z in zip(a,y))
        assert native_ring.jet_sub(a,y,base.mask)==tuple(base.sub(x,z) for x,z in zip(a,y))


def _exact_degree_sum(base, a, b, k):
    result=base.zero
    for j in range(k+1):
        result=base.add(result,base.mul(a[j],b[k-j]))
    return result
