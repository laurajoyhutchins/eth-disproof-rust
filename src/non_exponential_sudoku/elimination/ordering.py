from __future__ import annotations

from math import prod
from collections.abc import Sequence
from typing import Literal
from ..runtime.statistics import Counters
from ..runtime.budget import ModeBudget
from .factors import Factor

def select_variable(remaining: set[int], *, factors: Sequence[Factor],
                    domains: Sequence[range], order: Literal['min_fill', 'min_states'],
                    stats: Counters, budget: ModeBudget) -> int:
    # Domain-weighted min-fill: the primal graph has an edge between
    # each pair of modes in the same factor. Eliminating a mode joins all
    # its remaining neighbors. The rule is structural and deterministic;
    # it does not change the factor product or the truncated budget.
    # Fail before materializing giant adjacency cliques. The fill-order
    # analysis is computational work too, not a free oracle.
    clique_scans=sum(len(f.scope)**2 for f in factors)
    budget.order_work(clique_scans)
    adjacent: dict[int, set[int]] = {j:set() for j in remaining}
    for factor in factors:
        live=[j for j in factor.scope if j in remaining]
        for j in live:
            adjacent[j].update(k for k in live if j!=k)
    # Bound the total number of pair inspections for all candidates.
    if order=='min_fill':
        budget.order_work(sum(len(adjacent[v])**2 for v in remaining))
    def cost(v: int) -> tuple[int, ...]:
        incident=[f for f in factors if v in f.scope]
        union=set().union(*(f.scope for f in incident)) if incident else {v}
        out=union-{v}
        output_states=prod(len(domains[j]) for j in out)
        joined_states=prod(len(domains[j]) for j in union)
        fill=sum(len(domains[a])*len(domains[b])
                 for a in out for b in out if a<b and b not in adjacent[a])
        if order=='min_fill':
            return (fill,output_states,joined_states,len(out),v)
        return (output_states,joined_states,len(out),v)
    selected=min(remaining,key=cost)
    out=adjacent[selected]
    stats.mode_dp_order_fill_edges=getattr(stats,'mode_dp_order_fill_edges',0)+sum(
        1 for a in out for b in out if a<b and b not in adjacent[a])
    return selected
