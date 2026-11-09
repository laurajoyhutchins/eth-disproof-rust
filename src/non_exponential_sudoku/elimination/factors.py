from __future__ import annotations

from itertools import product
from dataclasses import dataclass
from collections.abc import Callable, Iterator, Mapping, Sequence
from ..core.modes import Mode
from ..core.lazy_coefficients import NestedCoords
from ..core.jets import NestedRing
from ..runtime.budget import ModeBudget
from ..runtime.cost_ledger import charge
from ..runtime.statistics import Counters

FactorKey = int | tuple[int, int]
ChildFactor = Callable[[FactorKey, tuple[int, ...], tuple[int, ...]], NestedCoords]

@dataclass
class Factor:
    scope: tuple[int,...]
    table: dict[tuple[int,...], dict[int, NestedCoords]]

class FactorBuilder:
    """Build actual recursively contracted local factors from a pure scope plan."""
    def __init__(self, *, modes: Sequence[Mode],
                 factor_scopes: Mapping[FactorKey, tuple[int, ...]],
                 domains: Sequence[range], ring: NestedRing, stats: Counters,
                 evaluate_child: ChildFactor, budget: ModeBudget) -> None:
        self.modes=modes
        self.factor_scopes=factor_scopes
        self.domains=domains
        self.R=ring
        self.p=ring.p
        self.stats=stats
        self.evaluate_child=evaluate_child
        self.budget=budget
        self.max_states=budget.max_states
        self.CapacityError=budget.CapacityError
        self.factors=budget.factors

    def active_components(self) -> Mapping[FactorKey, tuple[int, ...]]:
        # Connectivity is determined by the actual local factors, not just
        # by sharing a group. This detects exact packet-component splits.
        parent=list(range(len(self.modes)))
        def find(i: int) -> int:
            while parent[i]!=i:
                parent[i]=parent[parent[i]];i=parent[i]
            return i
        def union(a: int, b: int) -> None:
            a=find(a);b=find(b)
            if a!=b:parent[b]=a
        for scope in self.factor_scopes.values():
            for k in scope[1:]:union(scope[0],k)
        self.stats.mode_dp_components+=len({find(j) for j in range(len(self.modes))})
        return self.factor_scopes

    def admissible_scoped_assignments(
        self, scope: tuple[int, ...], label: str,
    ) -> Iterator[tuple[int, ...]]:
        """Stream precisely the local tuples with weighted degree < p.

        All mode weights are positive. Nonadmissible local assignments cannot
        participate in any global tuple, so no omitted contribution can be
        restored by multiplication or later elimination. The candidate bound
        counts admissible, not Cartesian-product, states.
        """
        weight_counts={0:1}
        for j in scope:
            nxt: dict[int, int] = {}
            w=self.modes[j].weight
            for total,count in weight_counts.items():
                for b in self.domains[j]:
                    self.budget.work()
                    degree=total+w*b
                    if degree>=self.p: break
                    nxt[degree]=min(self.max_states+1,nxt.get(degree,0)+count)
            if sum(nxt.values())>self.max_states:
                raise self.CapacityError(
                    f'Mode DP factor size limit ({label}: more than {self.max_states} admissible states)')
            weight_counts=nxt
        if not scope:
            yield ()
            return
        assignment=[0]*len(scope)
        budget=[self.p-1]*(len(scope)+1)
        last=len(scope)-1
        k=0
        while k>=0:
            if assignment[k]>=len(self.domains[scope[k]]) or \
                    self.modes[scope[k]].weight*assignment[k]>budget[k]:
                assignment[k]=0;k-=1
                if k>=0:assignment[k]+=1
                continue
            budget[k+1]=budget[k]-self.modes[scope[k]].weight*assignment[k]
            if k==last:
                yield tuple(assignment)
                assignment[k]+=1
            else:
                k+=1;assignment[k]=0

    def build(self, group_to_modes: Mapping[FactorKey, tuple[int, ...]]) -> bool:
        self.stats.mode_dp_factors+=len(group_to_modes)
        for group, scope in group_to_modes.items():
            scope=tuple(scope)
            tab: dict[tuple[int, ...], dict[int, NestedCoords]] = {}
            table_terms=0
            for assignment in self.admissible_scoped_assignments(scope, f'group {group}'):
                self.budget.charge_child()
                value=self.evaluate_child(group,scope,assignment)
                if value!=self.R.zero:
                    tab[assignment]={0:value}
                    table_terms+=1
                    charge("mode_factor_rows_retained")
                    self.budget.guard_build(len(tab),table_terms,'local child factor')
            self.factors.append(Factor(scope,tab))
            self.budget.guard_live()
            if not tab:return False
        return True
