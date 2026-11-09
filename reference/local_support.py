#!/usr/bin/env python3
"""Exact, polynomial-time tensor support reduction for generalized Sudoku.

Generalized arc consistency of the all-different factors is obtained by
bipartite matchings. Every removed cell/digit pair lacks support in at least
one Sudoku unit; every pinned bit is shared by *all* remaining values. Thus
pinning those wires preserves the complete solution count. This module has
no branching/search or solution enumeration and is not a Sudoku solver.
"""
from __future__ import annotations
from dataclasses import dataclass
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.band_network import BandNetwork
from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial


class LocalContradiction(ValueError):
    pass


def matching_possible(domains:list[int], n:int)->bool:
    """Exists a permutation of n digits, one allowed for each cell?"""
    claimed=[-1]*n
    def augment(cell:int,seen:list[bool])->bool:
        mask=domains[cell]
        while mask:
            bit=mask & -mask
            d=bit.bit_length()-1
            mask-=bit
            if not seen[d]:
                seen[d]=True
                if claimed[d]<0 or augment(claimed[d],seen):
                    claimed[d]=cell
                    return True
        return False
    for cell in sorted(range(n),key=lambda k:domains[k].bit_count()):
        if not augment(cell,[False]*n):return False
    return True


def _projected_domains_matching(puzzle:Puzzle):
    n=puzzle.side
    mask=(1<<n)-1
    domains=[1<<(v-1) if v else mask for v in puzzle.entries]
    rounds=0
    while True:
        rounds+=1
        changed=False
        for unit in puzzle.units():
            ds=[domains[cell] for cell in unit]
            if not matching_possible(ds,n):
                raise LocalContradiction('A Sudoku all-different factor has no completion')
            for j,cell in enumerate(unit):
                current=domains[cell]
                new=0
                allowed=current
                while allowed:
                    bit=allowed&-allowed
                    allowed-=bit
                    d=ds.copy();d[j]=bit
                    if matching_possible(d,n):new |= bit
                if not new:raise LocalContradiction('Empty digit support')
                if new != current:
                    domains[cell]=new
                    changed=True
        if not changed:break
    return tuple(domains),rounds


def projected_domains(puzzle:Puzzle, *, method='enhanced', limits=None, return_metrics=False):
    """Polynomial matching GAC with optional incremental exact-cover bookkeeping.

    `matching` retains the original full-pass reference; `incremental`
    applies only exact-cover forced placements; `enhanced` also projects
    unsupported all-different candidates using matching and an event queue.
    """
    if method not in ('matching','incremental','enhanced'):
        raise ValueError('Unknown propagation method')
    if method=='matching':
        domains,rounds=_projected_domains_matching(puzzle)
        metrics={'method':method,'remaining_candidates':sum(d.bit_count() for d in domains),
                 'initial_candidates':puzzle.side**3, 'matching_unit_scans':None,
                 'matching_checks':None, 'forced_placements':None,
                 'removed_candidates':puzzle.side**3-sum(d.bit_count() for d in domains)}
    else:
        from .exact_cover_propagation import (propagate, ExactCoverContradiction)
        try:
            state=propagate(puzzle,matching=method=='enhanced',
                            matching_possible=matching_possible,limits=limits)
        except ExactCoverContradiction as exc:
            raise LocalContradiction(str(exc)) from exc
        domains=tuple(state.domains)
        rounds=state.unit_scans if method=='enhanced' else 1
        metrics={'method':method,**state.metrics()}
    if return_metrics:
        return domains,rounds,metrics
    return domains,rounds


def pin_band_wires(puzzle:Puzzle, *, propagation='enhanced', limits=None):
    """Return exact residual tensor network after polynomial-time reductions."""
    domains,rounds,propagation_metrics=projected_domains(puzzle,method=propagation,limits=limits,return_metrics=True)
    old=BandNetwork.from_puzzle(puzzle)
    fixed={}
    free=[]
    for edge,(cell,bit) in enumerate(old.edge_cells):
        allowed=domains[cell]
        bits={((digit-1)>>bit)&1 for digit in range(1,puzzle.side+1)
              if allowed & (1<<(digit-1))}
        if len(bits)==1:fixed[edge]=next(iter(bits))
        else:free.append(edge)
    old_to_new={edge:i for i,edge in enumerate(free)}
    def restrict(vertex):
        positions=tuple(i for i,e in enumerate(vertex.ports) if e in old_to_new)
        ports=tuple(old_to_new[vertex.ports[i]] for i in positions)
        template=tuple(fixed.get(e,0) for e in vertex.ports)
        # Sudoku's original oracles are Boolean, independent of the
        # coefficient ring. For bounded arity, compile the reduced Boolean
        # factor once; this is the same oracle, not a SAT backtracker.
        # The cap prevents constructing exponential-size tables on large
        # generalized networks.
        if len(ports)<=12:
            ring=Padic(2,modulus_polynomial(2),1)
            table=bytearray(1<<len(ports))
            for mask in range(len(table)):
                entries=list(template)
                for i,pos in enumerate(positions):
                    entries[pos]=(mask>>i)&1
                table[mask]=int(vertex.oracle(tuple(entries),ring)!=ring.zero)
            def oracle(bits,R,table=bytes(table)):
                if len(bits)!=len(ports):raise ValueError('Arity mismatch')
                mask=sum(bit<<i for i,bit in enumerate(bits))
                return R.one if table[mask] else R.zero
        else:
            def oracle(bits,R):
                if len(bits)!=len(positions):raise ValueError('Arity mismatch')
                entries=list(template)
                for i,v in zip(positions,bits):entries[i]=v
                return vertex.oracle(tuple(entries),R)
        return Vertex(vertex.name,ports,oracle)
    net=Network([restrict(v) for v in old.net.left],
                [restrict(v) for v in old.net.right],len(free))
    net.validate()
    return net,{'original_wires':old.net.edges,'remaining_wires':net.edges,
                'pinned_wires':len(fixed),'domain_rounds':rounds,
                'undecided_cells':sum(d.bit_count()>1 for d in domains),
                'total_domain_options':sum(d.bit_count() for d in domains),
                'max_degree':max((len(v.ports) for v in net.left+net.right),default=0),
                'propagation':propagation_metrics}
