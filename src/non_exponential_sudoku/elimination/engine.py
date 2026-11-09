from __future__ import annotations

from math import prod
from contextlib import nullcontext
from ..runtime.cost_ledger import active_ledger
from collections.abc import Mapping, Sequence
from typing import Literal, cast
from ..core.algebra import Padic
from ..core.jets import JetRing, NestedRing
from ..core.lazy_coefficients import NestedCoords
from ..core.modes import Mode
from ..runtime.statistics import Counters
from ..runtime.config import ModeLimits

try:
    import native_sparse as _native_sparse
except ImportError:
    _native_sparse = None  # type: ignore[assignment]
from .factors import Factor, FactorBuilder, FactorKey, ChildFactor
from .polynomial import PolynomialOps
from .ordering import select_variable
from .scope_plan import inspect_scope
from ..runtime.budget import ModeBudget

class ModeEliminator:
    """One factor-elimination executor, with reference scan and sparse join strategies."""

    def __init__(self, modes: Sequence[Mode], groups: set[int],
                 R: Padic | JetRing, evaluate_child: ChildFactor,
                 stats: Counters, capacity_error: type[Exception], *,
                 factor_scopes: Mapping[tuple[int, int], tuple[int, ...]] | None = None,
                 order: Literal['min_fill', 'min_states'] = 'min_states',
                 join_strategy: Literal['adaptive', 'sparse', 'enumerate'] = 'adaptive',
                 limits: ModeLimits | None = None,
                 native_sparse: bool = True,
                 packet_row_caps: bool = False) -> None:
        if join_strategy not in ('adaptive','enumerate','sparse'):
            raise ValueError('Unknown mode factor join strategy')
        self.join_strategy=join_strategy
        self.native_sparse=bool(native_sparse)
        if order not in ('min_states','min_fill'):
            raise ValueError('Unknown variable elimination order')
        self.order=order
        self.modes=modes
        self.groups=tuple(sorted(groups))
        # The element depth is fixed by R for the duration of this elimination.
        self.R: NestedRing = cast(NestedRing, R)
        self.evaluate_child=evaluate_child
        self.stats=stats
        self.CapacityError=capacity_error
        self.domains=tuple(range(min(len(m.rows),(R.p-1)//m.weight)+1)
                           for m in modes)
        self.p=R.p
        limits = ModeLimits() if limits is None else limits
        self.factors: list[Factor] = []
        # Keys identify either whole groups or connected components within
        # groups. The component scopes partition each group's incident modes.
        self.factor_scopes: dict[FactorKey, tuple[int, ...]]
        if factor_scopes is None:
            self.factor_scopes={g:tuple(j for j,m in enumerate(modes)
                   if m.source==g or m.target==g) for g in self.groups}
        else:
            self.factor_scopes={key: scope for key, scope in factor_scopes.items()}
            for g in self.groups:
                assigned=[j for key,scope in self.factor_scopes.items()
                          if isinstance(key,tuple) and key[0]==g for j in scope]
                expected=[j for j,m in enumerate(modes)
                          if m.source==g or m.target==g]
                if sorted(assigned)!=sorted(expected):
                    raise ValueError(f'Component scopes do not partition group {g}')
        self.stats.mode_dp_variables+=len(modes)
        self.stats.mode_dp_groups+=len(groups)
        # Coefficient sizes include inherited Taylor variables; a conservative
        # Python-container allowance prevents silent huge allocation.
        coords=R.e
        ring: Padic | JetRing = R
        while isinstance(ring, JetRing):
            coords*=ring.q
            ring=cast(Padic | JetRing, ring.base)
        self.bytes_per_coefficient=max(64,(coords*R.p+7)//8+160)

        self.budget=ModeBudget(stats=self.stats,error=self.CapacityError,
                max_states=limits.max_factor_states,max_terms=limits.max_live_terms,
                max_operations=limits.max_operations,
                max_children=limits.max_child_contractions,
                max_bytes=limits.max_estimated_bytes,
                bytes_per_coefficient=self.bytes_per_coefficient)
        self.polynomials=PolynomialOps(self.R,self.p,self.budget)
        self.factor_builder=FactorBuilder(modes=self.modes,factor_scopes=self.factor_scopes,
                domains=self.domains,ring=self.R,stats=self.stats,
                evaluate_child=self.evaluate_child,budget=self.budget,
                packet_row_caps=packet_row_caps)
        self.factors=self.factor_builder.factors

    def _guard_live(self) -> None:
        self.budget.factors=self.factors
        self.budget.guard_live()

    def _join_factors_sparse(self, factors: Sequence[Factor]) -> Factor:
        """Exact support-aware natural joins over nonzero assignment rows.

        Unlike scanning the whole projected separator domain, join only rows
        with compatible shared-mode multiplicities.  The entries remain
        truncated generating polynomials in the *unchanged* coefficient ring.
        The positive-weight guard is exact for every partial assignment.
        """
        # Deterministic size/overlap ordering limits the maximum temporary
        # separator. This is a heuristic, not a width theorem.
        if self.native_sparse and _native_sparse is not None:
            return _native_sparse.join_factors_sparse(list(factors),self.modes,self.R,self.budget,self.stats)
        remaining=list(factors)
        remaining.sort(key=lambda f:(len(f.table),len(f.scope),f.scope))
        joined=remaining.pop(0)
        while remaining:
            js=set(joined.scope)
            def score(f: Factor) -> tuple[int, int, int, tuple[int, ...]]:
                overlap=len(js.intersection(f.scope))
                # Favor connected joins over Cartesian products; then table
                # size and projected scope are deterministic tie breakers.
                return (-overlap,len(joined.table)*len(f.table),
                        len(js.union(f.scope)),f.scope)
            idx=min(range(len(remaining)),key=lambda i:score(remaining[i]))
            nxt=remaining.pop(idx)
            union=tuple(sorted(set(joined.scope).union(nxt.scope)))
            shared=tuple(sorted(set(joined.scope).intersection(nxt.scope)))
            left_indices=tuple(joined.scope.index(j) for j in shared)
            right_indices=tuple(nxt.scope.index(j) for j in shared)
            right_only=tuple((j,nxt.scope.index(j)) for j in nxt.scope if j not in js)
            index: dict[tuple[int, ...], list[tuple[tuple[int, ...], dict[int, NestedCoords]]]] = {}
            for ra,rp in nxt.table.items():
                self.budget.work()
                key=tuple(ra[i] for i in right_indices)
                index.setdefault(key,[]).append((ra,rp))
            new_table: dict[tuple[int, ...], dict[int, NestedCoords]] = {}; new_terms=0
            for la,lp in joined.table.items():
                self.budget.work()
                lookup=tuple(la[i] for i in left_indices)
                for ra,rp in index.get(lookup,()):
                    self.budget.work()
                    a_map=dict(zip(joined.scope,la))
                    for j,at in right_only:a_map[j]=ra[at]
                    assignment=tuple(a_map[j] for j in union)
                    assigned_weight=sum(self.modes[j].weight*b
                                        for j,b in zip(union,assignment))
                    if assigned_weight>=self.p:continue
                    poly=self.polynomials.mul(lp,rp)
                    if not poly:continue
                    # Any future factors and eliminated variables have
                    # nonnegative degree, so impossible terms are discarded.
                    poly={d:v for d,v in poly.items() if d+assigned_weight<self.p}
                    if not poly:continue
                    if assignment in new_table:
                        # A natural join of maps with unique keys should
                        # never produce duplicate union assignments.
                        raise AssertionError('Duplicate natural-join row')
                    new_table[assignment]=poly
                    new_terms+=len(poly)
                    self.budget.guard_build(len(new_table),new_terms,'sparse separator join')
                    self.stats.mode_dp_sparse_join_rows+=1
            joined=Factor(union,new_table)
            if self.budget.growth_probe is not None:
                self.budget.growth_probe.joined(self.budget,joined)
            self.stats.mode_dp_sparse_joins+=1
            self.stats.mode_dp_peak_join_states=max(
                self.stats.mode_dp_peak_join_states,len(new_table))
            if not joined.table:break
        return joined

    def _eliminate_one_sparse(self, var: int, incident: list[Factor], rest: list[Factor]) -> None:
        # Multiplication is executed only on compatible nonzero rows. Summing
        # var then shifts by its weighted exponent exactly once, as in the
        # reference enumerator and dense projection path.
        if self.native_sparse and _native_sparse is not None:
            factor=_native_sparse.eliminate_one_sparse(var,list(incident),self.modes,
                  self.R,self.budget,self.stats)
            self.factors=rest+[factor]
            self.stats.mode_dp_eliminations+=1
            self.stats.mode_dp_sparse_eliminations+=1
            self.stats.mode_dp_max_scope=max(self.stats.mode_dp_max_scope,len(factor.scope))
            self._guard_live()
            return
        joined=self._join_factors_sparse(incident)
        out_scope=tuple(j for j in joined.scope if j!=var)
        out: dict[tuple[int, ...], dict[int, NestedCoords]] = {};out_terms=0
        position={j:k for k,j in enumerate(joined.scope)}
        for assignment,poly in joined.table.items():
            self.budget.work()
            b=assignment[position[var]]
            shift=self.modes[var].weight*b
            projected=tuple(assignment[position[j]] for j in out_scope)
            retained_weight=sum(self.modes[j].weight*x for j,x in zip(out_scope,projected))
            shifted={d+shift:v for d,v in poly.items()
                     if d+shift+retained_weight<self.p}
            if not shifted:continue
            if projected not in out:out[projected]={}
            prior=len(out[projected])
            self.polynomials.add(out[projected],shifted)
            out_terms+=len(out[projected])-prior
            if not out[projected]:
                del out[projected]
            self.budget.guard_build(len(out),out_terms,'sparse elimination output')
        self.factors=rest+[Factor(out_scope,out)]
        self.stats.mode_dp_eliminations+=1
        self.stats.mode_dp_sparse_eliminations+=1
        self.stats.mode_dp_max_scope=max(self.stats.mode_dp_max_scope,len(out_scope))
        self._guard_live()

    def _use_sparse_join(self, incident: Sequence[Factor]) -> bool:
        if self.join_strategy=='sparse':return True
        if self.join_strategy=='enumerate':return False
        # Sparse joins are most beneficial when zero-valued child factors
        # remove assignment rows. Large *raw* domain does not imply a fast
        # join, so the choice is based on actually observed support.
        for f in incident:
            raw=prod(len(self.domains[j]) for j in f.scope)
            if raw>1 and len(f.table)*3<raw*2:
                return True
        return False

    def _eliminate_one(self, var: int) -> None:
        step=inspect_scope(var, tuple(f.scope for f in self.factors))
        attached=set(step.incident)
        incident=[self.factors[i] for i in step.incident]
        rest=[f for i,f in enumerate(self.factors) if i not in attached]
        out_scope=step.output
        if self._use_sparse_join(incident):
            return self._eliminate_one_sparse(var,incident,rest)
        # Only assignments with remaining total weight below p can survive.
        # Avoid rejecting an exponentially large raw Cartesian product if
        # almost all assignments already exceed the global positive budget.
        out: dict[tuple[int, ...], dict[int, NestedCoords]] = {}
        out_terms=0
        # Every mode is eliminated exactly once; multiply the generating
        # polynomial by z^(weight*beta) at that elimination step.
        for out_assignment in self.factor_builder.admissible_scoped_assignments(out_scope, f'eliminating mode {var}'):
            assigned=dict(zip(out_scope,out_assignment))
            result: dict[int, NestedCoords] = {}
            for b in self.domains[var]:
                self.budget.work()
                assigned[var]=b
                weight=self.modes[var].weight*b
                if weight>=self.p:continue
                term={0:self.R.one}
                for factor in incident:
                    poly=factor.table.get(tuple(assigned[j] for j in factor.scope))
                    if not poly:
                        term={};break
                    term=self.polynomials.mul(term,poly)
                    if not term:break
                if term:
                    shifted={degree+weight:value for degree,value in term.items()
                             if degree+weight<self.p}
                    self.polynomials.add(result,shifted)
            if result:
                remaining_weight=sum(self.modes[j].weight*b for j,b in zip(out_scope,out_assignment))
                result={d:v for d,v in result.items() if d+remaining_weight<self.p}
            if result:
                out[out_assignment]=result
                out_terms+=len(result)
                self.budget.guard_build(len(out),out_terms,'elimination output')
        self.factors=rest+[Factor(out_scope,out)]
        self.stats.mode_dp_eliminations+=1
        self.stats.mode_dp_max_scope=max(self.stats.mode_dp_max_scope,len(out_scope))
        self._guard_live()

    def run(self) -> NestedCoords:
        ledger = active_ledger()
        with (ledger.phase("mode_elimination") if ledger is not None
              else nullcontext()):
            return self._run_with_probe()

    def _run_with_probe(self) -> NestedCoords:
        probe=self.budget.growth_probe
        if probe is not None:
            probe.begin(self.budget,self.modes,self.domains,self.R)
            probe.planned(self.budget,self.factor_scopes.values())
        try:
            answer=self._run_internal()
        except BaseException:
            if probe is not None:probe.end(self.budget,status="refused_or_failed")
            raise
        if probe is not None:probe.end(self.budget,status="completed")
        return answer

    def _run_internal(self) -> NestedCoords:
        groups=self.factor_builder.active_components()
        if not self.factor_builder.build(groups):return self.R.zero
        remaining=set(range(len(self.modes)))
        while remaining:
            selected=select_variable(remaining,factors=self.factors,domains=self.domains,order=self.order,stats=self.stats,budget=self.budget)
            self._eliminate_one(selected)
            remaining.remove(selected)
        # All scopes must now be empty. Product of surviving factor
        # polynomials convolves the independent mode-interaction components.
        poly={0:self.R.one}
        for factor in self.factors:
            if factor.scope:raise AssertionError('Mode variable survived elimination')
            poly=self.polynomials.mul(poly,factor.table.get((),{}))
            if not poly:break
        result=self.R.zero
        for v in poly.values():result=self.R.add(result,v)
        self.stats.mode_dp_final_polynomial_degree=max(poly,default=-1)
        return result
