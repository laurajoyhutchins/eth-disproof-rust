from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from collections.abc import Iterable, Sequence
from typing import TypeAlias, TypeVar
from .lazy_coefficients import CoefficientRing
from .flint_backend import (
    flint_enabled, flint_inverse_lift, flint_mul, flint_pow,
)
from ..runtime.budget import CapacityError
from ..runtime.cost_ledger import ring_call, native_call
from functools import lru_cache
try:
    import native_ring as _native_ring
except ImportError:
    _native_ring = None  # type: ignore[assignment]

RingCoords: TypeAlias = tuple[int, ...]
CoeffT = TypeVar("CoeffT")

def poly_remainder(a: int, b: int) -> int:
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length()-b.bit_length())
    return a


def poly_gcd(a: int,b: int) -> int:
    while b:
        a,b=b,poly_remainder(a,b)
    return a


def poly_square(a: int) -> int:
    x=0
    for i in range(a.bit_length()):
        if a>>i & 1: x ^= 1 << (2*i)
    return x


@lru_cache(maxsize=256)
def irreducible_mod_two(f: int, degree: int) -> bool:
    x=2
    y=x
    for j in range(1,degree+1):
        y=poly_remainder(poly_square(y),f)
        if j<=degree//2 and degree%j==0 and poly_gcd(y^x,f)!=1:
            return False
    return y==x


@lru_cache(None)
def modulus_polynomial(e: int) -> int:
    if e<2: raise ValueError('extension degree must be at least 2')
    for low in range(1,1<<e,2):
        f=(1<<e)|low
        if irreducible_mod_two(f,e): return f
    raise AssertionError('Irreducible polynomial must exist')


@dataclass(frozen=True)
class Padic:
    """Coordinates in Z/(2^p)[U]/(f), f irreducible modulo two."""
    e: int
    f: int
    p: int

    def __post_init__(self) -> None:
        if self.p<1 or self.f.bit_length()!=self.e+1 or not irreducible_mod_two(self.f,self.e):
            raise ValueError('Invalid coefficient ring')

    @property
    def mask(self) -> int:
        return (1 << self.p) - 1

    @property
    def zero(self) -> RingCoords:
        return (0,) * self.e

    @property
    def one(self) -> RingCoords:
        return (1,) + (0,) * (self.e - 1)
    def scalar(self,n: int) -> RingCoords:
        ring_call("scalar", self)
        return (n&self.mask,)+(0,)*(self.e-1)
    def basis(self, bits: int) -> RingCoords:
        ring_call("basis", self)
        return tuple((bits>>i)&1 for i in range(self.e))
    def lift(self,x: Iterable[int]) -> RingCoords:
        ring_call("lift", self)
        return tuple(c & self.mask for c in x)
    def add(self,a: RingCoords,b: RingCoords) -> RingCoords:
        ring_call("add", self, a, b)
        if _native_ring is not None:
            native_call("native_padic_add")
            return _native_ring.add(a,b,self.mask)
        return tuple((x+y)&self.mask for x,y in zip(a,b))
    def neg(self,a: RingCoords) -> RingCoords:
        ring_call("neg", self)
        return tuple((-x)&self.mask for x in a)
    def sub(self,a: RingCoords,b: RingCoords) -> RingCoords:
        ring_call("sub", self, a, b)
        if _native_ring is not None:
            native_call("native_padic_sub")
            return _native_ring.sub(a,b,self.mask)
        return tuple((x-y)&self.mask for x,y in zip(a,b))
    def mul(self,a: RingCoords,b: RingCoords) -> RingCoords:
        ring_call("mul", self, a, b)
        if flint_enabled():
            native_call("flint_padic_mul")
            return flint_mul(self, a, b)
        if _native_ring is not None:
            native_call("native_padic_mul")
            return _native_ring.mul(a,b,self.e,self.f,self.mask)
        p=self.p; mask=self.mask; e=self.e; f=self.f
        tmp=[0]*(2*e-1)
        for i,ai in enumerate(a):
            if ai:
                for j,bj in enumerate(b):
                    if bj: tmp[i+j] += ai*bj
        # f(U) monic; high terms removed in Z/2^p, NOT GF(2^e).
        for i in range(len(tmp)-1,e-1,-1):
            h=tmp[i]&mask
            if h:
                for j in range(e):
                    if (f>>j)&1: tmp[i-e+j] -= h
        return tuple(v&mask for v in tmp[:e])
    def pow(self,a: RingCoords,n: int) -> RingCoords:
        ring_call("pow", self)
        if n<0: return self.pow(self.inv(a),-n)
        if not n: return self.one
        if flint_enabled():
            native_call("flint_padic_pow")
            return flint_pow(self, a, n)
        r=self.one
        while n:
            if n&1: r=self.mul(r,a)
            a=self.mul(a,a); n>>=1
        return r
    def inv(self,a: RingCoords) -> RingCoords:
        ring_call("inv", self)
        if not any(v&1 for v in a): raise ZeroDivisionError('not a 2-adic unit')
        # Inverse modulo two via the little residue field, then Newton lift.
        bits=sum((c&1)<<i for i,c in enumerate(a))
        def fm(a: int,b: int) -> int:
            out=0
            for i in range(self.e):
                if b>>i&1: out ^= a<<i
            return poly_remainder(out,self.f)
        def fp(a: int,n: int) -> int:
            r=1
            while n:
                if n&1: r=fm(r,a)
                a=fm(a,a); n>>=1
            return r
        z=self.basis(fp(bits,(1<<self.e)-2))
        if flint_enabled():
            native_call("flint_padic_inv")
            return flint_inverse_lift(self, a, z)
        for _ in range(self.p.bit_length()+1):
            z=self.mul(z,self.sub(self.scalar(2),self.mul(a,z)))
        assert self.mul(a,z)==self.one
        return z
    def integer_quotient_2(self,a: RingCoords,v: int) -> RingCoords:
        if any(c%(1<<v) for c in a):
            raise ValueError('Not divisible by 2^v coordinatewise')
        return tuple(c>>v for c in a)
    def rational(self,x: Fraction | int) -> RingCoords:
        ring_call("rational", self)
        if not isinstance(x,Fraction): x=Fraction(x)
        k=v2(abs(x.numerator)) if x.numerator else 0
        j=v2(x.denominator)
        if x and k<j: raise ValueError('Rational not 2-adically integral')
        num=x.numerator>>k
        den=x.denominator>>j
        return self.scalar(((num * pow(den,-1,1<<self.p)) << (k-j)) & self.mask)


def v2(n: int) -> int:
    if n==0: raise ValueError('v2(0) undefined')
    return (abs(n)&-abs(n)).bit_length()-1


def p_add(A: Sequence[CoeffT], B: Sequence[CoeffT], R: CoefficientRing[CoeffT]) -> list[CoeffT]:
    n=max(len(A),len(B)); z=R.zero
    return [R.add(A[i] if i<len(A) else z, B[i] if i<len(B) else z) for i in range(n)]


def p_mul(A: Sequence[CoeffT], B: Sequence[CoeffT], R: CoefficientRing[CoeffT],
          truncate: int | None = None) -> list[CoeffT]:
    n=len(A)+len(B)-1
    if truncate is not None: n=min(n,truncate)
    out=[R.zero]*n
    for i,a in enumerate(A):
        for j,b in enumerate(B):
            if i+j<n and a!=R.zero and b!=R.zero:
                out[i+j]=R.add(out[i+j],R.mul(a,b))
    return out


def p_eval(poly: Sequence[RingCoords], z: RingCoords, R: Padic) -> RingCoords:
    total=R.zero
    for a in reversed(poly): total=R.add(R.mul(total,z),a)
    return total


def interpolate(points: Iterable[tuple[RingCoords, RingCoords]], R: Padic) -> list[RingCoords]:
    """Newton interpolation at residue-distinct points: all denominators units."""
    pol=[R.zero]; basis=[R.one]
    for z,val in points:
        delta=R.sub(val,p_eval(pol,z,R))
        denom=p_eval(basis,z,R)
        k=R.mul(delta,R.inv(denom))
        pol=p_add(pol,[R.mul(k,t) for t in basis],R)
        basis=p_mul(basis,[R.neg(z),R.one],R)
    return pol


def interp_points(R: Padic, count: int) -> list[RingCoords]:
    if count>2**R.e: raise CapacityError('Not enough residue-distinct field elements')
    return [R.basis(i) for i in range(count)]
