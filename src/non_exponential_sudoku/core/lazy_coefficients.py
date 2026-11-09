"""Experimental lazy coefficient oracle for exact truncated series circuits.

This is NOT a drop-in replacement for JetRing inside the recursive contractor.
It provides a measured prototype for the key open question: can computing
coefficients on demand and limiting the cache reduce workspace without excessive
recomputation?  Supports 2-adic and nested-JetRing *coefficient rings* without
changing their arithmetic; truncation is by requested coefficient index.
"""
from __future__ import annotations
from collections import OrderedDict
from dataclasses import dataclass
from collections.abc import Iterable
from typing import Generic, Protocol, TypeVar, TypeAlias

# Exact coefficients are finite tuples of integers, recursively nested by
# deformation depth. This excludes unrelated objects from the expression DAG.
NestedCoords: TypeAlias = tuple[int, ...] | tuple["NestedCoords", ...]

ValueT = TypeVar("ValueT")

class CoefficientRing(Protocol[ValueT]):
    """Coefficient operations. The element type cannot change within a DAG."""
    @property
    def zero(self) -> ValueT: ...
    def add(self, a: ValueT, b: ValueT) -> ValueT: ...
    def sub(self, a: ValueT, b: ValueT) -> ValueT: ...
    def mul(self, a: ValueT, b: ValueT) -> ValueT: ...
    def neg(self, a: ValueT) -> ValueT: ...
    def inv(self, a: ValueT) -> ValueT: ...

@dataclass(frozen=True,eq=False)
class Expression(Generic[ValueT]):
    op: str
    children: tuple[Expression[ValueT], ...] = ()
    value: tuple[ValueT, ...] = ()

    @staticmethod
    def coeffs(values: Iterable[ValueT]) -> Expression[ValueT]:
        return Expression('coeffs', value=tuple(values))
    def __add__(self,other: Expression[ValueT]) -> Expression[ValueT]:
        return Expression('add',(self,other))
    def __sub__(self,other: Expression[ValueT]) -> Expression[ValueT]:
        return Expression('sub',(self,other))
    def __mul__(self,other: Expression[ValueT]) -> Expression[ValueT]:
        return Expression('mul',(self,other))
    def inverse(self) -> Expression[ValueT]:
        return Expression('inv',(self,))

class CoefficientWorkExceeded(RuntimeError):
    """Hard guard on uncached recursive coefficient evaluation."""


class CoefficientOracle(Generic[ValueT]):
    def __init__(self, base: CoefficientRing[ValueT], q: int,
                 cache_limit: int = 0, miss_limit: int | None = None) -> None:
        if q < 1 or cache_limit < 0:raise ValueError('Invalid bounds')
        self.base=base
        self.q=q
        self.cache_limit=cache_limit
        self.miss_limit=miss_limit
        self.cache: OrderedDict[tuple[Expression[ValueT], int], ValueT] = OrderedDict()
        self.requests=0
        self.misses=0
        self.mul_ops=0
        self.max_cached=0
        self.max_stack=0
        self._stack=0

    def coefficient(self, expr: Expression[ValueT], degree: int) -> ValueT:
        if degree<0 or degree>=self.q:raise ValueError('Coefficient outside truncation')
        self.requests += 1
        key=(expr,degree)
        if key in self.cache:
            v=self.cache.pop(key)
            self.cache[key]=v
            return v
        if self.miss_limit is not None and self.misses >= self.miss_limit:
            raise CoefficientWorkExceeded('Coefficient oracle work budget exceeded')
        self.misses+=1
        self._stack+=1
        self.max_stack=max(self.max_stack,self._stack)
        R=self.base
        try:
            if expr.op=='coeffs':
                v=expr.value[degree] if degree<len(expr.value) else R.zero
            elif expr.op=='add':
                v=R.add(self.coefficient(expr.children[0],degree),
                        self.coefficient(expr.children[1],degree))
            elif expr.op=='sub':
                v=R.sub(self.coefficient(expr.children[0],degree),
                        self.coefficient(expr.children[1],degree))
            elif expr.op=='mul':
                v=R.zero
                for j in range(degree+1):
                    x=self.coefficient(expr.children[0],j)
                    if x==R.zero:continue
                    y=self.coefficient(expr.children[1],degree-j)
                    if y==R.zero:continue
                    v=R.add(v,R.mul(x,y))
                    self.mul_ops+=1
            elif expr.op=='inv':
                a=expr.children[0]
                if degree==0:
                    v=R.inv(self.coefficient(a,0))
                else:
                    acc=R.zero
                    for j in range(1,degree+1):
                        x=self.coefficient(a,j)
                        if x!=R.zero:
                            y=self.coefficient(expr,degree-j)
                            if y!=R.zero:
                                acc=R.add(acc,R.mul(x,y));self.mul_ops+=1
                    inv0=self.coefficient(expr,0)
                    v=R.neg(R.mul(inv0,acc));self.mul_ops+=1
            else:raise ValueError(expr.op)
        finally:
            self._stack-=1
        if self.cache_limit:
            self.cache[key]=v
            if len(self.cache)>self.cache_limit:self.cache.popitem(last=False)
            self.max_cached=max(self.max_cached,len(self.cache))
        return v

    def series(self,expr: Expression[ValueT]) -> tuple[ValueT, ...]:
        return tuple(self.coefficient(expr,k) for k in range(self.q))
