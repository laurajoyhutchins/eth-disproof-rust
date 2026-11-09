from __future__ import annotations

from dataclasses import dataclass, field
from itertools import product
from collections.abc import Iterable, Mapping, Sequence
from typing import Callable, cast
from .algebra import Padic, RingCoords
from .jets import JetRing, NestedRing
from .lazy_coefficients import NestedCoords

TensorRing = Padic | JetRing
from ..runtime.budget import CapacityError
from ..runtime.cost_ledger import charge

@dataclass(frozen=True)
class Vertex:
    name: str
    ports: tuple[int,...]
    oracle: Callable[[tuple[int,...], TensorRing], NestedCoords]


def _vertex_oracle(vertex: Vertex, bits: tuple[int, ...], ring: TensorRing) -> NestedCoords:
    charge("vertex_oracle_calls")
    return vertex.oracle(bits,ring)


@dataclass
class Network:
    left: list[Vertex]
    right: list[Vertex]
    edges: int
    leaf_plan: LeafPlan | None = field(default=None, repr=False, compare=False)
    def validate(self) -> None:
        lc=[0]*self.edges; rc=[0]*self.edges
        for side,counts in ((self.left,lc),(self.right,rc)):
            for vertex in side:
                for edge in vertex.ports:
                    if edge<0 or edge>=self.edges: raise AssertionError('Invalid port index')
                    counts[edge]+=1
        if any(x!=1 for x in lc+rc): raise AssertionError('Every edge must have two endpoints')
    def direct(self,R: TensorRing,limit: int = 20) -> NestedCoords:
        if self.edges>limit: raise CapacityError(f'Direct leaf has {self.edges} edges; limit is {limit}')
        B = cast(NestedRing, R)
        ans=B.zero
        for assignment in product((0,1),repeat=self.edges):
            charge("exhaustive_assignments_enumerated")
            z=B.one
            for vertex in self.left+self.right:
                bits=tuple(assignment[k] for k in vertex.ports)
                z=B.mul(z,_vertex_oracle(vertex,bits,R))
                if z==B.zero: break
            ans=B.add(ans,z)
        return ans


@dataclass(frozen=True)
class LeafStep:
    """Topology-only elimination instruction; indices name factor tables."""
    incident: tuple[int, ...]
    output_id: int
    out_scope: tuple[int, ...]
    # For small separators, lookup[mask][factor] is (index if bit=0,
    # index if bit=1). Larger separators use the compact position vectors.
    lookup: tuple[tuple[tuple[int, int], ...], ...] | None
    positions: tuple[tuple[int, ...], ...]


@dataclass(frozen=True)
class LeafPlan:
    """Reusable Boolean elimination schedule; contains no coefficient values."""
    edges: int
    input_scopes: tuple[tuple[int, ...], ...]
    max_width: int
    steps: tuple[LeafStep, ...]
    lookup_budget: int = 8192


def compile_leaf_plan(edges: int, scopes: Sequence[Sequence[int]], max_width: int = 16,
                      *, lookup_budget: int = 8192) -> LeafPlan | None:
    """Compile the existing min-width leaf order without evaluating oracles.

    Return None when the reference algorithm would fall back to direct
    contraction. Index tables are bounded; large separators retain a compact
    mapping and calculate their bit indices at evaluation time.
    """
    normalized_scopes: tuple[tuple[int, ...], ...] = tuple(tuple(scope) for scope in scopes if scope)
    if any(len(scope) > max_width for scope in normalized_scopes):
        return None
    factors: dict[int, tuple[int, ...]] = {index: scope for index, scope in enumerate(normalized_scopes)}
    remaining = set(range(edges))
    next_id = len(factors)
    steps: list[LeafStep] = []
    remaining_lookups = lookup_budget
    while remaining:
        def incident(e: int) -> tuple[int, ...]:
            return tuple(k for k, scope in factors.items() if e in scope)
        def key(e: int) -> tuple[int, int, int]:
            inc = incident(e)
            union = set().union(*(factors[k] for k in inc)) if inc else set()
            return (len(union) - 1, len(inc), e)
        edge = min(remaining, key=key)
        inc = incident(edge)
        out_scope = tuple(sorted(set().union(*(factors[k] for k in inc)) - {edge}))
        if len(out_scope) > max_width:
            return None
        positions = tuple(tuple(out_scope.index(x) if x != edge else -1
                                for x in factors[k]) for k in inc)
        size = (1 << len(out_scope)) * len(inc)
        lookup: tuple[tuple[tuple[int, int], ...], ...] | None = None
        if size <= remaining_lookups:
            rows = []
            for mask in range(1 << len(out_scope)):
                row = []
                for mapping in positions:
                    zero_ix = one_ix = 0
                    for j, pos in enumerate(mapping):
                        if pos < 0:
                            one_ix |= 1 << j
                        elif (mask >> pos) & 1:
                            zero_ix |= 1 << j
                            one_ix |= 1 << j
                    row.append((zero_ix, one_ix))
                rows.append(tuple(row))
            lookup = tuple(rows)
            remaining_lookups -= size
        steps.append(LeafStep(inc, next_id, out_scope, lookup, positions))
        for k in inc:
            del factors[k]
        if out_scope:
            factors[next_id] = out_scope
        next_id += 1
        remaining.remove(edge)
    return LeafPlan(edges, normalized_scopes, max_width, tuple(steps), lookup_budget)


def estimated_coefficient_bytes(ring: TensorRing) -> int:
    """Conservative size estimate for one live (possibly nested) ring value."""
    coordinates = ring.e
    nested: TensorRing = ring
    while isinstance(nested, JetRing):
        coordinates *= nested.q
        nested = cast(TensorRing, nested.base)
    return max(64, coordinates * ((ring.p + 7) // 8 + 40) + 128)


def _check_leaf_factor_budget(
    entries: int, ring: TensorRing, max_factor_bytes: int | None,
) -> None:
    # Include simultaneously retained input tables and the next output table.
    # This is an estimated storage guard, not a resident-memory measurement.
    if (max_factor_bytes is not None and
            entries * estimated_coefficient_bytes(ring) > max_factor_bytes):
        raise CapacityError("Leaf factor memory budget exceeded")


def _execute_leaf_plan(plan: LeafPlan, tables: dict[int, tuple[NestedCoords, ...]], ring: TensorRing,
                       max_factor_bytes: int | None = None) -> NestedCoords:
    """Run exact elimination using topology compiled independently of values."""
    R = cast(NestedRing, ring)
    zero = R.zero
    one = R.one
    scalar: NestedCoords = one
    for step in plan.steps:
        if not step.incident:
            scalar = R.mul(scalar, R.scalar(2))
            continue
        involved = [tables.pop(k) for k in step.incident]
        _check_leaf_factor_budget(
            sum(len(table) for table in tables.values()) +
            sum(len(table) for table in involved) +
            (1 << len(step.out_scope)), ring, max_factor_bytes)
        out: list[NestedCoords] = []
        if step.lookup is not None:
            for row in step.lookup:
                charge("leaf_elimination_rows")
                acc = zero
                for bit in (0, 1):
                    term = one
                    for table, indices in zip(involved, row):
                        value = table[indices[bit]]
                        if value is zero:
                            term = zero
                            break
                        if term is one:
                            term = value
                        elif value is not one:
                            term = R.mul(term, value)
                        if term == zero:
                            break
                    acc = R.add(acc, term)
                out.append(acc)
        else:
            for mask in range(1 << len(step.out_scope)):
                charge("leaf_elimination_rows")
                acc = zero
                for bit in (0, 1):
                    term = one
                    for positions, table in zip(step.positions, involved):
                        ix = 0
                        for offset, pos in enumerate(positions):
                            ix |= ((bit if pos < 0 else (mask >> pos) & 1) << offset)
                        value = table[ix]
                        if value is zero:
                            term = zero
                            break
                        if term is one:
                            term = value
                        elif value is not one:
                            term = R.mul(term, value)
                        if term == zero:
                            break
                    acc = R.add(acc, term)
                out.append(acc)
        if step.out_scope:
            tables[step.output_id] = tuple(out)
        else:
            scalar = R.mul(scalar, out[0])
            if scalar == zero:
                return zero
    if tables:
        raise AssertionError('Elimination left unresolved factors')
    return scalar



def eliminate_leaf(net: Network, R: TensorRing, max_edges: int = 20, max_width: int = 16, *,
                   plan: LeafPlan | None = None,
                   max_factor_bytes: int | None = None) -> NestedCoords:
    """Exact factor-table elimination at a PAPER-ALLOWED exhaustive leaf.

    The parent call and all Cauchy/mode/Hermite transforms are unchanged.
    This is only a different evaluation order of the same Boolean contraction
    at the base case. It computes all local tables and sums a variable after
    multiplying its incident tables. The edge limit caps *exhaustive fallback*,
    not safe elimination with a supplied factor-memory budget. If a factor or
    separator is too wide, the bounded direct fallback may explicitly refuse.
    """
    B = cast(NestedRing, R)
    if max_factor_bytes is not None and max_factor_bytes < 1:
        raise ValueError('Leaf factor memory budget must be positive')
    # The edge cap limits exhaustive enumeration, not structural elimination.
    # For a larger network, require the existing explicit factor-memory guard
    # before evaluating any vertex or allocating a factor table.
    if net.edges > max_edges and max_factor_bytes is None:
        raise CapacityError('Large elimination requires an explicit factor-memory budget')
    if plan is not None:
        scopes = tuple(v.ports for v in net.left + net.right if v.ports)
        if plan.edges != net.edges or plan.input_scopes != scopes or plan.max_width != max_width:
            raise ValueError('Leaf plan does not match this network topology')
        B_plan = cast(NestedRing, R)
        tables: dict[int, tuple[NestedCoords, ...]] = {}
        scalar: NestedCoords = B_plan.one
        index = 0
        for vertex in net.left + net.right:
            if not vertex.ports:
                scalar = B_plan.mul(scalar, _vertex_oracle(vertex,(), R))
                if scalar == B_plan.zero:
                    return scalar
                continue
            _check_leaf_factor_budget(
                sum(len(table) for table in tables.values()) +
                (1 << len(vertex.ports)), R, max_factor_bytes)
            values = tuple(_vertex_oracle(vertex,tuple((assignment >> j) & 1
                                               for j in range(len(vertex.ports))), R)
                           for assignment in range(1 << len(vertex.ports)))
            if all(value == B_plan.zero for value in values):
                return B_plan.zero
            tables[index] = values
            index += 1
        return B_plan.mul(scalar, _execute_leaf_plan(
            plan, tables, R, max_factor_bytes=max_factor_bytes))

    # Factor is (ordered edge scope, dense table indexed by bit position).
    factors: list[tuple[tuple[int, ...], tuple[NestedCoords, ...]]] = []
    scalar=B.one
    for v in net.left+net.right:
        ports=tuple(v.ports)
        if not ports:
            scalar=B.mul(scalar,_vertex_oracle(v,(),R))
            if scalar==B.zero:return scalar
            continue
        if len(ports)>max_width:return net.direct(R,max_edges)
        _check_leaf_factor_budget(
            sum(len(table) for _, table in factors) + (1 << len(ports)),
            R, max_factor_bytes)
        values=tuple(_vertex_oracle(v,tuple((index>>i)&1 for i in range(len(ports))),R)
                     for index in range(1<<len(ports)))
        if all(t==B.zero for t in values):return B.zero
        factors.append((ports,values))

    remaining=set(range(net.edges))
    while remaining:
        # Greedily eliminate the variable with smallest resulting union scope.
        # Ties use index order, so verification is reproducible.
        incident_by_var={e:[k for k,(scope,table) in enumerate(factors) if e in scope]
                         for e in remaining}
        def key(e: int) -> tuple[int, int, int]:
            inc=incident_by_var[e]
            scope=set().union(*(factors[i][0] for i in inc)) if inc else set()
            return len(scope)-1,len(inc),e
        edge=min(remaining,key=key)
        incident=set(incident_by_var[edge])
        if not incident:
            # An unconstrained wire has two values; this is 2 x scalar.
            scalar=B.mul(scalar,B.scalar(2))
            remaining.remove(edge)
            continue
        out_scope=tuple(sorted(set().union(*(factors[i][0] for i in incident)) - {edge}))
        if len(out_scope)>max_width:
            return net.direct(R,max_edges)
        _check_leaf_factor_budget(
            sum(len(table) for _, table in factors) + (1 << len(out_scope)),
            R, max_factor_bytes)
        # The two complete assignments differing in the selected wire are
        # summed exactly, with no satisfiability pruning or approximation.
        compiled: list[tuple[list[int], tuple[NestedCoords, ...]]] = []
        for i in sorted(incident):
            scope,table=factors[i]
            positions=[out_scope.index(x) if x!=edge else -1 for x in scope]
            compiled.append((positions,table))
        out: list[NestedCoords] = []
        for mask in range(1<<len(out_scope)):
            charge("leaf_elimination_rows")
            acc=B.zero
            for bit in (0,1):
                term=B.one
                for positions,table in compiled:
                    ix=0
                    for offset,pos in enumerate(positions):
                        ix |= ((bit if pos<0 else (mask>>pos)&1)<<offset)
                    term=B.mul(term,table[ix])
                    if term==B.zero:break
                acc=B.add(acc,term)
            out.append(acc)
        factors=[f for i,f in enumerate(factors) if i not in incident]
        if out_scope:
            factors.append((out_scope,tuple(out)))
        else:
            scalar=B.mul(scalar,out[0])
            if scalar==B.zero:return scalar
        remaining.remove(edge)
    if factors:raise AssertionError('Elimination left unresolved variables')
    return scalar


def indicator_entry(table: Mapping[tuple[int, ...], int]) -> Callable[[tuple[int, ...], TensorRing], NestedCoords]:
    # Only for microtests: direct table lookup, not ordinary Sudoku solving.
    tab={tuple(k):int(v) for k,v in table.items()}
    def oracle(bits: tuple[int, ...], R: TensorRing) -> NestedCoords:
        return R.scalar(tab.get(tuple(bits),0))
    return oracle


def simple_network(
    edges: int,
    left_factors: Iterable[tuple[Iterable[int], Mapping[tuple[int, ...], int]]],
    right_factors: Iterable[tuple[Iterable[int], Mapping[tuple[int, ...], int]]],
) -> Network:
    left=[Vertex(f'L{i}',tuple(ports),indicator_entry(tab)) for i,(ports,tab) in enumerate(left_factors)]
    right=[Vertex(f'R{i}',tuple(ports),indicator_entry(tab)) for i,(ports,tab) in enumerate(right_factors)]
    net=Network(left,right,edges); net.validate(); return net
