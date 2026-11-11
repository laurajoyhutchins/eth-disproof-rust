from __future__ import annotations

from .children import make_child, ceil_ninth_tenths
from .workspaces import FrameWorkspace
from typing import TYPE_CHECKING
from collections.abc import Sequence
from contextlib import nullcontext
from time import perf_counter_ns
from ..runtime.cost_ledger import charge
from ..core.network import Network, TensorRing
from ..core.packing import Packing
from ..core.modes import Mode
from ..core.lazy_coefficients import NestedCoords
from .children import ChildComponent
from .packets import EvaluationContext
from .zero_support import certify_zero
from .pre_factor_support import prepare_factor_support, PreparedFactorSupport
from ..runtime.cache import BudgetedLRU
if TYPE_CHECKING:
    from .engine import ContractionEngine

class ChildEvaluator:
    def __init__(self, contractor: ContractionEngine, net: Network, packing: Packing,
                 modes: list[Mode], t: int, z: NestedCoords, ring: TensorRing,
                 depth: int, coordinate: int, context: EvaluationContext) -> None:
        self.contractor=contractor
        self.net=net
        self.packing=packing
        self.modes=modes
        self.t=t
        self.z=z
        self.ring=ring
        self.depth=depth
        self.coordinate=coordinate
        self.context=context
        workspace = contractor._frames.get(depth)
        if workspace is None:
            workspace = FrameWorkspace(
                cache_policy=contractor.config.recursion.compiled_plans,
                leaf=contractor.config.leaf,
                shared_cache=contractor.shared_cache,
            )
            contractor._frames[depth] = workspace
        self._workspace = workspace
        self._pre_factor_cache: BudgetedLRU[object, PreparedFactorSupport] | None = (
            BudgetedLRU(contractor.config.recursion.pre_factor_support_cache,
                        shared=contractor.shared_cache)
            if contractor.config.recursion.zero_support.pre_factor else None)

    def prove_zero(self, group: int, assignment: Sequence[int], *,
                   mode_indices: Sequence[int] | None = None,
                   component: ChildComponent | None = None) -> bool:
        """Prove factor support empty before exact child preparation."""
        c = self.contractor
        policy = c.config.recursion.zero_support
        cache = self._pre_factor_cache
        if cache is None:
            return False
        selected_modes = (self.modes if mode_indices is None else
                          [self.modes[j] for j in mode_indices])
        before_evictions = self._workspace.plans.evictions
        plan, hit = self._workspace.get_plan(
            self.net, self.packing, group, self.coordinate, component)
        c.stats.child_plan_cache_evictions += (
            self._workspace.plans.evictions - before_evictions)
        c.stats.child_plan_cache_peak_estimated_bytes = max(
            c.stats.child_plan_cache_peak_estimated_bytes,
            self._workspace.plans.peak_bytes)
        if hit:
            c.stats.child_plan_cache_hits += 1
        else:
            c.stats.compiled_child_plans += 1
        c.stats.pre_factor_attempts += 1
        charge('pre_factor_support_attempts')
        started = perf_counter_ns() if c.work_trace is not None else 0
        prepared = cache.get(plan)
        if prepared is None:
            c.stats.pre_factor_cache_misses += 1
            prepared = prepare_factor_support(plan, self.ring, policy)
            if prepared is None:
                c.stats.pre_factor_unsupported += 1
                return False
            c.stats.pre_factor_kept_evaluations += prepared.kept_evaluations
            charge('pre_factor_support_rows', prepared.kept_evaluations)
            cache.put(plan, prepared, prepared.estimated_owned_bytes())
            c.stats.pre_factor_cache_peak_bytes = max(
                c.stats.pre_factor_cache_peak_bytes, cache.peak_bytes)
        else:
            c.stats.pre_factor_cache_hits += 1
        result = prepared.certify(selected_modes, tuple(assignment), policy)
        c.stats.pre_factor_evaluated_rows += result.evaluated_rows
        charge('pre_factor_support_rows', result.evaluated_rows)
        if result.verdict == 'unsupported':
            c.stats.pre_factor_unsupported += 1
        if result.verdict == 'zero':
            # The paper path checks this invariant for all exact children.
            # A certified child does not materialize; check its compiled
            # geometry instead so a zero proof cannot bypass admission.
            if c.config.schedule == 'paper':
                if 32 * plan.edges > 3 * self.net.edges:
                    raise AssertionError('Certified child violates 3M/32 wire bound')
                largest = max((len(v.ports) for v in plan.kept), default=0)
                largest = max(largest, *(len(v.edges) for v in plan.packet_ports), 0)
                c.stats.checked_child_edges += 1
                c.stats.maximum_observed_child_degree = max(
                    c.stats.maximum_observed_child_degree, largest)
                if largest > ceil_ninth_tenths(c.config.s):
                    raise AssertionError('Certified child degree invariant violated')
            c.stats.pre_factor_certificates += 1
            charge('pre_factor_zero_certificates')
            if c.work_trace is not None:
                c.work_trace.observe(
                    operation='child_zero_certificate',
                    topology=(tuple(v.ports for v in plan.kept),
                              tuple(v.edges for v in plan.packet_ports)),
                    exact_input=(id(self.net), id(self.packing), id(self.ring),
                                 self.coordinate, group, component,
                                 tuple(selected_modes), tuple(assignment), self.t, self.z),
                    started_ns=started, output=self.ring.zero)
            return True
        return False

    def close_pre_factor(self) -> None:
        if self._pre_factor_cache is not None:
            self._pre_factor_cache.clear()

    def evaluate(self, group: int, assignment: Sequence[int], *,
                 mode_indices: Sequence[int] | None = None,
                 component: ChildComponent | None = None) -> NestedCoords:
        c=self.contractor
        trace = c.work_trace
        started = perf_counter_ns() if trace is not None else 0
        if mode_indices is None:
            selected_modes=self.modes
        else:
            selected_modes=[self.modes[j] for j in mode_indices]
        with (c.cost_ledger.phase("child_construction") if c.cost_ledger is not None
              else nullcontext()):
            if c.config.recursion.child_plans:
                before_evictions = self._workspace.plans.evictions
                plan,hit=self._workspace.get_plan(self.net,self.packing,group,
                                                   self.coordinate,component)
                c.stats.child_plan_cache_evictions += (
                    self._workspace.plans.evictions - before_evictions)
                c.stats.child_plan_cache_peak_estimated_bytes = max(
                    c.stats.child_plan_cache_peak_estimated_bytes,
                    self._workspace.plans.peak_bytes,
                )
                if hit:
                    c.stats.child_plan_cache_hits+=1
                else:
                    c.stats.compiled_child_plans+=1
                child=plan.instantiate(selected_modes,tuple(assignment),self.t,self.z,
                                       self.ring,self.context)
            else:
                child=make_child(self.net,self.packing,selected_modes,
                                       tuple(assignment),self.t,self.z,self.ring,
                                       group,self.coordinate,self.context,component=component)
        if c.config.schedule=='paper':
            if 32*child.edges>3*self.net.edges:
                raise AssertionError('Live child violates 3M/32 wire bound')
            c.stats.checked_child_edges+=1
            largest=max((len(v.ports) for v in child.left+child.right),default=0)
            c.stats.maximum_observed_child_degree=max(
                c.stats.maximum_observed_child_degree,largest)
            if largest>ceil_ninth_tenths(c.config.s):
                raise AssertionError('Live child degree invariant violated')
        c.stats.child_cache_misses+=1
        c.stats.child_networks+=1
        charge("child_networks_constructed")
        # Only a local-support depletion certificate may bypass recursion.
        # Unproven or over-budget children retain their exact evaluator.
        policy = c.config.recursion.zero_support
        if policy.enabled and (not policy.pre_factor or c.config.mode.strategy == 'enumerate'):
            c.stats.zero_support_attempts += 1
            certificate = certify_zero(child, self.ring, policy)
            c.stats.zero_support_evaluated_rows += certificate.evaluated_rows
            if certificate.verdict == 'unsupported':
                c.stats.zero_support_unsupported += 1
            elif certificate.verdict == 'zero':
                c.stats.zero_support_certificates += 1
                if trace is not None:
                    trace.observe(
                        operation='child_zero_certificate',
                        topology=(tuple(v.ports for v in child.left),
                                  tuple(v.ports for v in child.right)),
                        exact_input=(id(self.net), id(self.packing), id(self.ring),
                                     self.coordinate, group, component,
                                     tuple(selected_modes), tuple(assignment), self.t, self.z),
                        started_ns=started, output=self.ring.zero,
                    )
                return self.ring.zero
        # Topology identifies incidence only. Distinct coefficient assignments
        # may construct the same topology yet require different exact answers.
        if trace is None:
            return c.contract(child,precision=self.ring.p,depth=self.depth+1,
                              ring=self.ring if c.config.recovery.method=='jet' else None,
                              _validated=c.config.recursion.child_plans)
        topology = (tuple(v.ports for v in child.left),
                    tuple(v.ports for v in child.right))
        exact_input = (id(self.net), id(self.packing), id(self.ring),
                       self.coordinate, group, component,
                       tuple(selected_modes), tuple(assignment), self.t, self.z)
        try:
            result = c.contract(child,precision=self.ring.p,depth=self.depth+1,
                                ring=self.ring if c.config.recovery.method=='jet' else None,
                                _validated=c.config.recursion.child_plans)
        except Exception:
            trace.observe(operation="child_contraction", topology=topology,
                          exact_input=exact_input, started_ns=started,
                          output=None, failed=True)
            raise
        trace.observe(operation="child_contraction", topology=topology,
                      exact_input=exact_input, started_ns=started, output=result)
        return result
