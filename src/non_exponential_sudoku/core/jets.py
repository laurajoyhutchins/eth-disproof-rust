"""Exact finite 2-adic Taylor jets for nested Appendix-D recursion.

Elements are polynomials of degree < q in z over the existing unramified
2-adic extension ring: A_p[z]/(z**q). All coefficients are exact modulo 2**p.
This is a quotient-ring evaluation of the paper's Cauchy/mode identity, not
an interpolation heuristic or a separate Sudoku search algorithm. Nested jets
represent independent deformation variables at successive recursion levels.
"""
from __future__ import annotations

from fractions import Fraction
from collections.abc import Sequence
from typing import Protocol, cast
from .algebra import Padic, RingCoords
from ..runtime.cost_ledger import ring_call, native_call
from .lazy_coefficients import NestedCoords

JetValue = tuple[NestedCoords, ...]

class NestedRing(Protocol):
    """Opaque exact coefficient ring for a single recursive jet layer.

    Its values are finite nested integer tuples. The parent ring fixes the
    admissible nesting depth, which the type checker cannot encode alone.
    """
    e: int
    f: int
    p: int
    @property
    def zero(self) -> NestedCoords: ...
    @property
    def one(self) -> NestedCoords: ...
    def scalar(self, n: int) -> NestedCoords: ...
    def basis(self, bits: int) -> NestedCoords: ...
    def lift(self, value: NestedCoords) -> NestedCoords: ...
    def add(self, a: NestedCoords, b: NestedCoords) -> NestedCoords: ...
    def sub(self, a: NestedCoords, b: NestedCoords) -> NestedCoords: ...
    def neg(self, a: NestedCoords) -> NestedCoords: ...
    def mul(self, a: NestedCoords, b: NestedCoords) -> NestedCoords: ...
    def inv(self, a: NestedCoords) -> NestedCoords: ...
    def pow(self, a: NestedCoords, n: int) -> NestedCoords: ...
    def rational(self, value: Fraction | int) -> NestedCoords: ...

try:
    import native_ring as _nr
except ImportError:
    _nr = None  # type: ignore[assignment]


class JetRing:
    e: int
    f: int
    p: int
    q: int
    depth: int
    def __init__(self, base: Padic | JetRing, q: int) -> None:
        if q < 1:
            raise ValueError('Taylor length must be >=1')
        # Coefficient depth stays fixed for this ring; the cast erases only
        # that depth index and retains the exact tuple-valued ABI.
        self.base: NestedRing = cast(NestedRing, base)
        self.q = q
        self.e, self.f, self.p = base.e, base.f, base.p
        self.depth = 1 + getattr(base, "depth", 0)
        self._native_base = hasattr(base, "mask")  # a single Padic coefficient layer
        # Resolve native function dispatch once per jet ring, rather than on
        # every operation. Nested jets deliberately retain the generic ring.
        native = _nr if self._native_base else None
        self._native_add = getattr(native, 'jet_add', None)
        self._native_sub = getattr(native, 'jet_sub', None)
        self._native_neg = getattr(native, 'jet_neg', None)
        self._native_mul = getattr(native, 'jet_mul', None)
        self.zero: JetValue = (base.zero,) * q
        self.one: JetValue = (base.one,) + (base.zero,) * (q-1)
        self.variable: JetValue = ((base.zero, base.one) + (base.zero,) * (q-2)) if q>1 else self.zero

    def scalar(self, value: int) -> JetValue:
        ring_call("scalar", self)
        return (self.base.scalar(value),) + self.zero[1:]

    def basis(self, bits: int) -> JetValue:
        ring_call("basis", self)
        return (self.base.basis(bits),) + self.zero[1:]

    def lift(self, value: NestedCoords) -> JetValue:
        ring_call("lift", self)
        if len(value)==self.q and all(isinstance(x,tuple) for x in value):
            return tuple(self.base.lift(cast(NestedCoords, v)) for v in value)
        if len(value)==self.e and all(isinstance(x,int) for x in value):
            return (self.base.lift(value),)+self.zero[1:]
        raise ValueError('Cannot lift value into Taylor jet ring')

    def add(self,a: JetValue,b: JetValue) -> JetValue:
        ring_call("add", self)
        if len(a)!=self.q or len(b)!=self.q:
            raise ValueError('jet degree mismatch')
        # Do not return a raw operand on zero/one shortcuts: public Padic
        # arithmetic normalizes even noncanonical integer representatives.
        if self._native_add is not None:
            native_call("native_jet_add")
            return cast(JetValue, self._native_add(a,b,getattr(self.base,"mask")))
        B=self.base
        return tuple(B.add(x,y) for x,y in zip(a,b))

    def sub(self,a: JetValue,b: JetValue) -> JetValue:
        ring_call("sub", self)
        if len(a)!=self.q or len(b)!=self.q:
            raise ValueError('jet degree mismatch')
        if self._native_sub is not None:
            native_call("native_jet_sub")
            return cast(JetValue, self._native_sub(a,b,getattr(self.base,"mask")))
        B=self.base
        return tuple(B.sub(x,y) for x,y in zip(a,b))

    def neg(self,a: JetValue) -> JetValue:
        ring_call("neg", self)
        if self._native_neg is not None:
            native_call("native_jet_neg")
            return cast(JetValue, self._native_neg(a,getattr(self.base,"mask")))
        B=self.base
        return tuple(B.neg(x) for x in a)

    def mul(self,a: JetValue,b: JetValue) -> JetValue:
        ring_call("mul", self)
        if len(a)!=self.q or len(b)!=self.q:
            raise ValueError('jet degree mismatch')
        # Multiplication by the ring's canonical zero remains exact even
        # when the other operand uses a noncanonical integer representative.
        if a is self.zero or b is self.zero:
            return self.zero
        if self._native_mul is not None:
            native_call("native_jet_mul")
            return cast(JetValue, self._native_mul(a,b,self.e,self.f,getattr(self.base,"mask")))
        B=self.base
        z=B.zero
        ia=[i for i,x in enumerate(a) if x!=z]
        ib=[j for j,x in enumerate(b) if x!=z]
        if not ia or not ib:return self.zero
        out=[z]*self.q
        add=B.add;mul=B.mul
        for i in ia:
            x=a[i]
            for j in ib:
                if i+j>=self.q:break
                out[i+j]=add(out[i+j],mul(x,b[j]))
        return tuple(out)

    def inv(self,a: JetValue) -> JetValue:
        ring_call("inv", self)
        B=self.base
        inv0=B.inv(a[0])
        ans=[inv0]
        for k in range(1,self.q):
            value=B.zero
            for j in range(1,k+1):
                if a[j]!=B.zero and ans[k-j]!=B.zero:
                    value=B.add(value,B.mul(a[j],ans[k-j]))
            ans.append(B.neg(B.mul(inv0,value)))
        return tuple(ans)

    def pow(self,a: JetValue,n: int) -> JetValue:
        ring_call("pow", self)
        if n<0:
            return self.pow(self.inv(a),-n)
        ans=self.one
        while n:
            if n&1:ans=self.mul(ans,a)
            n>>=1
            if n:a=self.mul(a,a)
        return ans

    def rational(self,x: Fraction | int) -> JetValue:
        ring_call("rational", self)
        return (self.base.rational(x),)+self.zero[1:]


def precision_ring(ring: Padic | JetRing, precision: int) -> Padic | JetRing:
    """Recreate a (possibly nested) jet ring at a larger 2-adic precision."""
    from .algebra import Padic
    if isinstance(ring, JetRing):
        return JetRing(precision_ring(cast(Padic | JetRing, ring.base), precision), ring.q)
    if isinstance(ring, Padic):
        return Padic(ring.e, ring.f, precision)
    raise TypeError(f"Unexpected coefficient ring {type(ring)!r}")


def embed_element(value: NestedCoords, source_ring: Padic | JetRing,
                  target_ring: Padic | JetRing) -> NestedCoords:
    """Canonical *coordinate lift* followed by constant embedding in new jets.

    This is deliberately not advertised as a ring homomorphism from modulo
    2**p to modulo 2**p': canonical integer-coordinate representatives do
    not preserve all modular identities. The paper constructs entry routines
    that lift a particular already-created tensor entry, not an abstract
    quotient-ring homomorphism.
    """
    from .algebra import Padic
    if isinstance(target_ring, JetRing) and target_ring.depth > getattr(source_ring, 'depth', 0):
        return (embed_element(value, source_ring, cast(Padic | JetRing, target_ring.base)),) + target_ring.zero[1:]
    if isinstance(source_ring, JetRing) and isinstance(target_ring, JetRing):
        if source_ring.q != target_ring.q or source_ring.depth != target_ring.depth:
            raise ValueError('Cannot change existing Taylor length during lift')
        return tuple(embed_element(cast(NestedCoords, v), cast(Padic | JetRing, source_ring.base),
                                   cast(Padic | JetRing, target_ring.base)) for v in value)
    if isinstance(source_ring, Padic) and isinstance(target_ring, Padic):
        if source_ring.e != target_ring.e or source_ring.f != target_ring.f:
            raise ValueError('Incompatible 2-adic extension rings')
        return target_ring.lift(cast(RingCoords, value))
    raise TypeError('Illegal coefficient-ring depth reduction or unrelated ring')


def flatten_element(value: NestedCoords, ring: Padic | JetRing) -> RingCoords:
    """Ordered integer-coordinate vector for exact rational Hermite recovery."""
    if isinstance(ring, JetRing):
        return tuple(x for v in value
                     for x in flatten_element(cast(NestedCoords, v),
                                              cast(Padic | JetRing, ring.base)))
    return cast(RingCoords, tuple(value))


def unflatten_element(coords: Sequence[int], ring: Padic | JetRing) -> NestedCoords:
    """Reconstruct the coefficient vector after coordinatewise recovery."""
    if isinstance(ring, JetRing):
        dimension = len(flatten_element(ring.base.zero, cast(Padic | JetRing, ring.base)))
        if len(coords) != ring.q * dimension:
            raise ValueError('Wrong nested Hermite coordinate count')
        return tuple(unflatten_element(coords[i*dimension:(i+1)*dimension],
                                       cast(Padic | JetRing, ring.base))
                     for i in range(ring.q))
    if len(coords) != ring.e:
        raise ValueError('Wrong extension coordinate count')
    return tuple(coords)
