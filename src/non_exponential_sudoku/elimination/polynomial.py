from __future__ import annotations

from collections.abc import Mapping
from typing import Generic, TypeVar
from ..core.lazy_coefficients import CoefficientRing
from ..runtime.budget import ModeBudget

ValueT = TypeVar("ValueT")

class PolynomialOps(Generic[ValueT]):
    """Exact truncated sparse generating-polynomial algebra over any coefficient ring.

    The formal budget degree is NOT a Taylor-jet variable or a 2-adic digit.
    """
    def __init__(self, ring: CoefficientRing[ValueT], degree_cap: int, budget: ModeBudget) -> None:
        self.R=ring
        self.p=degree_cap
        self.budget=budget

    def add(self, target: dict[int, ValueT], source: Mapping[int, ValueT]) -> None:
        for degree,value in source.items():
            if degree>=self.p:continue
            self.budget.work()
            got=self.R.add(target.get(degree,self.R.zero),value)
            if got==self.R.zero: target.pop(degree,None)
            else: target[degree]=got

    def mul(self, a: Mapping[int, ValueT], b: Mapping[int, ValueT]) -> dict[int, ValueT]:
        if not a or not b:return {}
        result: dict[int, ValueT] = {}
        # Iterate over sparse polynomials, never allocate dense arrays of p
        # nested-jet values.  This exact convolution is truncated at p.
        for ia,va in a.items():
            for ib,vb in b.items():
                degree=ia+ib
                if degree>=self.p:continue
                self.budget.work()
                value=self.R.mul(va,vb)
                if value==self.R.zero:continue
                updated=self.R.add(result.get(degree,self.R.zero),value)
                if updated==self.R.zero:result.pop(degree,None)
                else:result[degree]=updated
                self.budget.guard_build(1,len(result),'polynomial convolution')
        return result
