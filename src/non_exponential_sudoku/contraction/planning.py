from __future__ import annotations

from dataclasses import dataclass
from collections.abc import Mapping, Sequence
from typing import Literal
from ..core.network import Network
from ..core.packing import Packing
from ..core.modes import Mode
from .children import ChildComponent, child_components

@dataclass(frozen=True)
class FactorSpec:
    group: int
    component_index: int
    mode_indices: tuple[int, ...]
    component: ChildComponent | None

    @property
    def key(self) -> tuple[int, int]:
        return (self.group, self.component_index)


@dataclass(frozen=True)
class FactorizationPlan:
    # A None scope mapping means the original whole-group ModeEliminator ABI.
    factors: tuple[FactorSpec, ...]
    factorization: str
    max_arity_before: int
    max_arity_after: int
    total_local_arity_after: int
    split_components: int

    @property
    def factor_scopes(self) -> dict[tuple[int, int], tuple[int, ...]] | None:
        if self.factorization == 'whole':
            return None
        return {spec.key: spec.mode_indices for spec in self.factors}

    @property
    def components(self) -> dict[tuple[int, int], ChildComponent | None]:
        return {spec.key: spec.component for spec in self.factors}


def build_factorization_plan(net: Network, packing: Packing, modes: Sequence[Mode],
                             coordinate: int, occupied: set[int],
                             affected: Mapping[int, Sequence[int]], *,
                             strategy: Literal['whole', 'components'] = 'components',
                             max_components: int = 20_000) -> FactorizationPlan:
    """Construct the *exact* group/component partition, without mutation.

    Raises ComponentCapacityExceeded when the split-count guard
    would refuse. The caller maps this to its public CapacityError.
    """
    if strategy not in ('whole', 'components'):
        raise ValueError('factorization strategy must be whole or components')
    if max_components < 1:
        raise ValueError('max_components must be positive')
    specs=[]
    before=after=total=split=0
    for g in sorted(occupied):
        incident=tuple(affected[g])
        before=max(before,len(incident))
        if strategy=='whole':
            specs.append(FactorSpec(g,0,incident,None))
            after=max(after,len(incident))
            continue
        partition=child_components(net,packing,g,coordinate)
        assigned: list[tuple[int, ...]] = []
        for comp in partition:
            packets=set(comp.packets)
            assigned.append(tuple(j for j in incident if modes[j].packet in packets))
        if len(partition)==1 or not incident or \
                max((len(scope) for scope in assigned),default=0)>=len(incident):
            specs.append(FactorSpec(g,0,incident,None))
            after=max(after,len(incident))
            total+=len(incident)
            continue
        # Unsplit factors do not count toward this resource guard.
        if len(specs)+len(partition)>max_components:
            raise ComponentCapacityExceeded('Mode DP component-count limit',
                                            before=before,after=after,total=total)
        if sorted(j for scope in assigned for j in scope)!=sorted(incident):
            raise AssertionError('Mode-to-child-component partition incomplete')
        for k,(comp,scope) in enumerate(zip(partition,assigned)):
            specs.append(FactorSpec(g,k,scope,comp))
            after=max(after,len(scope))
            total+=len(scope)
            split+=1
    return FactorizationPlan(tuple(specs),strategy,before,after,total,split)


class ComponentCapacityExceeded(RuntimeError):
    """Internal refusal with partial accounting for stable error reporting."""
    def __init__(self, message: str, *, before: int = 0, after: int = 0, total: int = 0) -> None:
        super().__init__(message)
        self.before=before
        self.after=after
        self.total=total
