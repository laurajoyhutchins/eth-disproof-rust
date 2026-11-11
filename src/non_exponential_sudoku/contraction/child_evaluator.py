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
from .packet_degree import (
    PacketDegreeZero, impossible_packet_target_degree, packet_target_row_capacity,
)
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
        self._row_capacity: dict[tuple[int, int], int] | None = None

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
        if len(selected_modes) != len(assignment):
            raise ValueError("one multiplicity is required per selected mode")
        # A packet's target coefficient of total degree d has at most one
        # target-variable contribution per retained Y-row. Certify d>rows
        # *before* allocating any child Network, prepared PacketEntry,
        # native leaf, or coefficient dictionary.
        degree_witness: PacketDegreeZero | None = None
        if any(mode.target == group and beta > 0
               for mode, beta in zip(selected_modes, assignment)):
            if self._row_capacity is None:
                self._row_capacity = packet_target_row_capacity(
                    self.net, self.packing, self.coordinate,
                )
            degree_witness = impossible_packet_target_degree(
                selected_modes, assignment, group=group,
                row_capacity=self._row_capacity, component=component,
            )
        if degree_witness is not None:
            c.stats.packet_degree_zero_certificates += 1
            charge("packet_degree_zero_certificates")
            if trace is not None:
                trace.observe(
                    operation="packet_degree_zero_certificate",
                    topology=(degree_witness.packet_id, degree_witness.group,
                              degree_witness.available_rows),
                    exact_input=(id(self.net), id(self.packing), id(self.ring),
                                 self.coordinate, group, component,
                                 tuple(selected_modes), tuple(assignment), self.t, self.z),
                    started_ns=started, output=self.ring.zero,
                )
            return self.ring.zero
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
        if policy.enabled:
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
