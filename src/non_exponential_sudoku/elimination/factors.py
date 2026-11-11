from __future__ import annotations

from dataclasses import dataclass
from collections.abc import Callable, Mapping, Sequence
from ..core.modes import Mode
from ..core.mode_assignments import iter_mode_assignments
from ..core.lazy_coefficients import NestedCoords
from ..core.jets import NestedRing
from ..runtime.budget import ModeBudget
from ..runtime.cost_ledger import charge
from ..runtime.statistics import Counters

FactorKey = int | tuple[int, int]
ChildFactor = Callable[[FactorKey, tuple[int, ...], tuple[int, ...]], NestedCoords]
ZeroProver = Callable[[FactorKey, tuple[int, ...], tuple[int, ...]], bool]

@dataclass
class Factor:
    scope: tuple[int,...]
    table: dict[tuple[int,...], dict[int, NestedCoords]]

class FactorBuilder:
    """Build actual recursively contracted local factors from a pure scope plan."""
    def __init__(self, *, modes: Sequence[Mode],
                 factor_scopes: Mapping[FactorKey, tuple[int, ...]],
                 domains: Sequence[range], ring: NestedRing, stats: Counters,
                 evaluate_child: ChildFactor, budget: ModeBudget,
                 packet_row_caps: bool = False,
                 prove_zero: ZeroProver | None = None) -> None:
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
        self.packet_row_caps=packet_row_caps
        self.prove_zero=prove_zero

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

    def build(self, group_to_modes: Mapping[FactorKey, tuple[int, ...]]) -> bool:
        self.stats.mode_dp_factors+=len(group_to_modes)
        for group, scope in group_to_modes.items():
            scope=tuple(scope)
            tab: dict[tuple[int, ...], dict[int, NestedCoords]] = {}
            table_terms=0
            group_id = group if isinstance(group, int) else group[0]
            assignments = iter_mode_assignments(
                self.modes, self.p, scope=scope,
                target_groups=(group_id,) if self.packet_row_caps else (),
                domains=self.domains, max_states=self.max_states,
                capacity_error=self.CapacityError, label=f'group {group}',
                work=self.budget.work,
            )
            for assignment in assignments:
                if self.prove_zero is not None and self.prove_zero(group, scope, assignment):
                    continue
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
