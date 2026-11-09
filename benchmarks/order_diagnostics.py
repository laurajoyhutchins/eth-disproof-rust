"""Non-executing structural comparison of DLX-like minimum column support
against predicted intermediate tensor-factor sizes. No algorithm substitution.

The support proxy is the number of dense local factor rows incident to the
mode. For sparse factors this is only an upper-bound proxy; use measured
support in any future decision rule. Output state costs assume binary modes.
"""
from __future__ import annotations
from itertools import combinations
from math import prod
from .native_dlx_cases import grid_edges


def simulate_elimination(factor_scopes,mode_count,method='size_estimate'):
    if method not in ('minimum_column','size_estimate','min_fill'):
        raise ValueError('Unknown diagnostic rule')
    factors=[frozenset(scope) for scope in factor_scopes]
    remaining=set(range(mode_count))
    order=[]
    max_scope=0
    max_projected_states=0
    sum_projected_states=0
    while remaining:
        def score(v):
            incident=[f for f in factors if v in f]
            union=set().union(*incident) if incident else {v}
            output=union-{v}
            projected=2**len(output)
            dense_support=sum(2**len(f) for f in incident)
            neighbors={k:set() for k in remaining}
            for f in factors:
                for j in f:
                    neighbors[j].update(f-{j})
            fill=sum(1 for a,b in combinations(sorted(output),2) if b not in neighbors[a])
            if method=='minimum_column':
                return (dense_support,projected,v)
            if method=='min_fill':
                return (fill,projected,dense_support,v)
            return (projected,dense_support,v)
        v=min(remaining,key=score)
        incident=[f for f in factors if v in f]
        union=set().union(*incident) if incident else {v}
        output=frozenset(union-{v})
        max_scope=max(max_scope,len(output))
        max_projected_states=max(max_projected_states,2**len(output))
        sum_projected_states+=2**len(output)
        factors=[f for f in factors if v not in f]+[output]
        remaining.remove(v)
        order.append(v)
    return {'method':method,'order':order,'max_projected_scope':max_scope,
      'max_projected_factor_states':max_projected_states,
      'sum_projected_factor_states':sum_projected_states,
      'assumptions':'binary domain, dense support upper-bound proxy, no arithmetic performed'}


def compare():
    rows=[]
    for side in (3,4,5):
        edges=grid_edges(side)
        factor_scopes=[tuple(j for j,(a,b) in enumerate(edges) if i in (a,b))
                      for i in range(side*side)]
        rows.append({'network':f'grid-{side}x{side}','modes':len(edges),
          'strategies':[simulate_elimination(factor_scopes,len(edges),method)
           for method in ('minimum_column','size_estimate','min_fill')]})
    return {'schema_version':'1.0.0','results':rows,
       'conclusion':'Projected intermediate sizes are structural envelopes; no change to production ordering'}

if __name__=='__main__':
    import json
    print(json.dumps(compare(),indent=2))
