"""Bounded coefficient memoization for *actual* implicit Appendix-D packet tensors.

This is an evaluation representation for one new Taylor indeterminate, not
an alternative contraction identity. The coefficient ring (Padic or nested
JetRing) stays unchanged. Expression nodes represent exact ring operations,
with lazy coefficient evaluation and per-context bounded memoization.

Scope: intermediate packet arithmetic, not recursive child tensor outputs;
it does not yet avoid dense inherited coefficient ring elements or prove a
space/time bound for the complete theorem schedule.
"""
from __future__ import annotations
from fractions import Fraction
from collections.abc import Sequence
from .jets import JetRing
from .algebra import Padic
from typing import cast
from .lazy_coefficients import (
    Expression, CoefficientOracle, CoefficientWorkExceeded, NestedCoords,
)

PacketExpression = Expression[NestedCoords]


class PacketCoefficientCapacityError(RuntimeError):
    pass


class LazyPacketJet:
    """Exact formal power-series operations with on-demand coefficients.

    Construct once per deformation (t, z, precision, parent coefficient
    ring). No memoized value crosses any of those boundaries. The maximum
    resident *coefficient cache* is bounded; expression DAG size is
    separately counted and guarded.  Values are Expression nodes only.
    """
    def __init__(self, dense_jet: JetRing, cache_limit: int, *, node_limit: int = 250_000,
                 miss_limit: int = 2_000_000, checkpoint_coordinates: int = 0) -> None:
        if not isinstance(dense_jet, JetRing):
            raise TypeError('Packet laziness requires a dense JetRing reference')
        if min(cache_limit, node_limit, miss_limit) < 0 or node_limit == 0 or miss_limit == 0:
            raise ValueError('Invalid capacity bounds')
        self.reference=dense_jet
        self.base=dense_jet.base
        self.e,self.f,self.p,self.q=dense_jet.e,dense_jet.f,dense_jet.p,dense_jet.q
        self.depth=dense_jet.depth
        self.oracle=CoefficientOracle(self.base,self.q,cache_limit=cache_limit, miss_limit=miss_limit)
        self.node_limit=node_limit
        if checkpoint_coordinates<0:raise ValueError('Invalid checkpoint budget')
        self.checkpoint_budget=checkpoint_coordinates
        self.checkpoint_used=0
        self.checkpoint_count=0
        self.base_coordinates=self.e
        inherited=self.base
        while isinstance(inherited, JetRing):
            self.base_coordinates*=inherited.q
            inherited=inherited.base
        self.miss_limit=miss_limit
        self.nodes=0
        self.materializations=0
        self._constants: dict[NestedCoords, PacketExpression] = {}
        self.zero=self._const(self.base.zero)
        self.one=self._const(self.base.one)
        self.variable=self._node('coeffs', value=(self.base.zero,self.base.one)) if self.q>1 else self.zero

    def _node(self, op: str, children: tuple[PacketExpression, ...] = (),
              value: tuple[NestedCoords, ...] = ()) -> PacketExpression:
        self.nodes+=1
        if self.nodes>self.node_limit:
            raise PacketCoefficientCapacityError('Packet expression DAG node budget exceeded')
        return Expression(op,tuple(children),tuple(value))

    def _const(self,value: NestedCoords) -> PacketExpression:
        # Nested ring coefficients are tuples and hashable.
        if value not in self._constants:
            self._constants[value]=self._node('coeffs',value=(value,))
        return self._constants[value]

    def from_dense(self,value: tuple[NestedCoords, ...]) -> PacketExpression:
        if value==self.reference.zero:return self.zero
        if value==self.reference.one:return self.one
        if value==self.reference.variable:return self.variable
        if not isinstance(value,tuple) or len(value)!=self.q:
            raise TypeError('Jet shape incompatible with lazy packet ring')
        return self._node('coeffs',value=value)

    def scalar(self, n: int) -> PacketExpression:return self._const(self.base.scalar(n))
    def basis(self, b: int) -> PacketExpression:return self._const(self.base.basis(b))
    def rational(self, v: Fraction | int) -> PacketExpression:return self._const(self.base.rational(v))
    def lift(self, v: tuple[NestedCoords, ...]) -> PacketExpression:return self.from_dense(self.reference.lift(v))

    def add(self, a: PacketExpression, b: PacketExpression) -> PacketExpression:
        if a is self.zero:return b
        if b is self.zero:return a
        return self._node('add',(a,b))
    def sub(self, a: PacketExpression, b: PacketExpression) -> PacketExpression:
        if b is self.zero:return a
        if a is b:return self.zero
        return self._node('sub',(a,b))
    def neg(self, a: PacketExpression) -> PacketExpression:
        if a is self.zero:return a
        return self.sub(self.zero,a) if a is not self.zero else a
    def mul(self, a: PacketExpression, b: PacketExpression) -> PacketExpression:
        if a is self.zero or b is self.zero:return self.zero
        if a is self.one:return b
        if b is self.one:return a
        return self._node('mul',(a,b))
    def inv(self, a: PacketExpression) -> PacketExpression:
        if a is self.one:return a
        return self._node('inv',(a,))
    def pow(self, a: PacketExpression, n: int) -> PacketExpression:
        if n<0:return self.pow(self.inv(a),-n)
        out=self.one
        while n:
            if n&1:out=self.mul(out,a)
            n>>=1
            if n:a=self.mul(a,a)
        return out

    def checkpoint(self, expr: PacketExpression) -> PacketExpression:
        """Replace a frequently reused DAG by its exact q coefficients.

        This is a bounded, precision-local materialization, intentionally
        restricted to Cauchy and cross-mode polynomials. It never shortcuts
        the recursive mode sum or evaluates a child contraction directly.
        """
        cost=self.q*self.base_coordinates
        if self.checkpoint_used+cost>self.checkpoint_budget:
            return expr
        coeff=self.materialize(expr)
        self.checkpoint_used+=cost
        self.checkpoint_count+=1
        return self._node('coeffs',value=coeff)

    def materialize(self, expr: PacketExpression) -> tuple[NestedCoords, ...]:
        self.materializations+=1
        try:
            return self._materialize(expr)
        except CoefficientWorkExceeded as exc:
            raise PacketCoefficientCapacityError(str(exc)) from exc

    def _materialize(self, expr: PacketExpression) -> tuple[NestedCoords, ...]:
        result: list[NestedCoords] = []
        for k in range(self.q):
            # Guard pathological repeated recomputation. Refuse rather than
            # silently falling back to dense or asserting an asymptotic bound.
            if self.oracle.misses>=self.miss_limit:
                raise PacketCoefficientCapacityError('Packet coefficient miss budget exceeded')
            result.append(self.oracle.coefficient(expr,k))
            if self.oracle.misses>self.miss_limit:
                raise PacketCoefficientCapacityError('Packet coefficient miss budget exceeded')
        return tuple(result)
