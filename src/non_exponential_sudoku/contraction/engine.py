from __future__ import annotations

from math import isqrt
from contextlib import nullcontext
from typing import cast, overload
from collections.abc import Mapping, Sequence
from ..core.algebra import Padic, RingCoords, modulus_polynomial, v2, interpolate, interp_points
from ..core.network import Network, TensorRing, eliminate_leaf
from ..core.packing import pack, audit_packing, LabelPair, Packing
from ..core.modes import Mode, mode_catalog
from ..core.lazy_coefficients import NestedCoords
from ..core.jets import JetRing, precision_ring
from .children import child_edge_audit, ceil_ninth_tenths
from ..recovery.hermite import tapered_recover, tapered_recover_over_ring
from ..recovery.streaming import StreamingHermite
from ..runtime.statistics import Counters
from ..runtime.config import ContractorConfig
from ..runtime.budget import CapacityError
from ..runtime.cost_ledger import CostLedger
from ..runtime.work_trace import WorkTrace
from ..runtime.cache import SharedCacheBudget
from .deformation import DeformationExecution
from .workspaces import FrameWorkspace
from .valuation_cache import ValuationCache

def paper_schedule_parameters(s: int, log_s: int, depth: int) -> tuple[int, int, int, int]:
    """Literal paper schedule, independent of ring allocation and recursion state.

    `log_s` is the exact bit-length parameter used by the paper schedule.
    Symbolic-size tests can check the schedule without constructing a ring.
    """
    divisor = max(1, isqrt(log_s))
    leaf_threshold = (s + divisor - 1) // divisor
    active = log_s // ((128 * 1024) * (1 << depth))
    accumulated = 2 * sum(
        log_s // ((128 * 1024) * (1 << level))
        for level in range(depth + 1)
    )
    return 64, accumulated, active, leaf_threshold


class ContractionEngine(DeformationExecution):
    """Thin recursive orchestration for the exact research contraction.

    Mathematical transforms, mode elimination, and resource accounting live in
    dedicated modules. The experimental schedules do not prove ETH asymptotics.
    """

    def __init__(self, config: ContractorConfig, *, cost_ledger: CostLedger | None = None,
                 work_trace: WorkTrace | None = None) -> None:
        if not isinstance(config,ContractorConfig):
            raise TypeError('ContractionEngine requires a ContractorConfig')
        self.config = config
        self.cost_ledger = cost_ledger
        self.work_trace = work_trace
        self.lambda_ = max(1, (config.s - 1).bit_length())
        self.e = max(2, 4 * self.lambda_)
        if config.schedule in ('micro', 'geometry64'):
            self.e = max(self.e, 5)
        self.f = modulus_polynomial(self.e)
        self.stats = Counters()
        self._frames: dict[int, FrameWorkspace] = {}
        self._active_contract_calls = 0
        self.shared_cache: SharedCacheBudget | None = (
            SharedCacheBudget(config.recursion.shared_cache_bytes)
            if config.recursion.shared_cache_bytes is not None else None
        )

    def _leaf(self, net: Network, ring: TensorRing) -> NestedCoords:
        ledger = self.cost_ledger
        if ledger is not None:
            with ledger.phase("leaf"):
                ledger.charge("leaf_calls")
                return self._leaf_impl(net, ring)
        return self._leaf_impl(net, ring)

    def _leaf_impl(self, net: Network, ring: TensorRing) -> NestedCoords:
        self.stats.leaves += 1
        if self.config.leaf.strategy=='eliminate':
            policy = self.config.leaf
            plan = net.leaf_plan
            if (plan is not None and (plan.max_width != policy.max_width
                    or plan.lookup_budget != policy.lookup_entries)):
                plan = None
            if self.config.recursion.native_leaf:
                try:
                    import native_recursive
                except ImportError as exc:
                    raise RuntimeError('native_leaf requested without native_recursive extension') from exc
                if self.cost_ledger is not None:
                    self.cost_ledger.native("native_leaf_elimination")
                return native_recursive.eliminate_leaf(
                    net, ring, policy.limit, max_width=policy.max_width,
                    plan=plan, max_factor_bytes=policy.max_factor_bytes)
            return eliminate_leaf(
                net, ring, policy.limit, max_width=policy.max_width,
                plan=plan, max_factor_bytes=policy.max_factor_bytes)
        return net.direct(ring,self.config.leaf.limit)

    def params(self, depth: int, M: int) -> tuple[int, int, int, int]:
        if self.config.schedule in ('micro', 'geometry64'):
            # Geometry64 implements the literal packing identity, not the
            # paper's asymptotic schedule or its input hypotheses.
            groups = 2 if self.config.schedule == 'micro' else 64
            if depth < self.config.micro_active_depth:
                slots = 1 if groups == 2 else 2
                return groups, slots, 1, self.config.leaf.micro_threshold
            return groups, 0, 1, M
        return paper_schedule_parameters(self.config.s, self.lambda_, depth)

    def contract_complete(self, net: Network, precision: int | None = None) -> NestedCoords:
        """Explicit exact *exhaustive* completion reference, with no wire cap.

        This is NOT Appendix D, NOT subexponential and NEVER selected as a
        silent fallback by contract(). It enumerates 2**M wire assignments,
        returns an element modulo 2**p, and requires finite total oracles.
        Its purpose is an independently countable termination/cost baseline.
        """
        net.validate()
        p=self.config.precision if precision is None else precision
        if p<1:
            raise ValueError('precision must be positive')
        R=Padic(self.e,self.f,p)
        if self.cost_ledger is not None:
            with self.cost_ledger.frame(depth=0,wires=net.edges,precision=p,
                                        ring_depth=0,schedule="exhaustive"):
                with self.cost_ledger.phase("exhaustive"):
                    return net.direct(R,net.edges)
        return net.direct(R,net.edges)

    def contract(self, net: Network, precision: int | None = None, depth: int = 0,
                 ring: TensorRing | None = None, *, _validated: bool = False) -> NestedCoords:
        # Workspaces share parent network objects across sibling children. Keep
        # them during recursive calls but never retain them after the outermost
        # contraction, even when a child raises or a resource guard refuses.
        self._active_contract_calls += 1
        try:
            ledger = self.cost_ledger
            if ledger is not None:
                with ledger.frame(depth=depth, wires=net.edges,
                                  precision=self.config.precision if precision is None else precision,
                                  ring_depth=getattr(ring, "depth", 0), schedule=self.config.schedule):
                    return self._contract_impl(net, precision, depth, ring, _validated=_validated)
            return self._contract_impl(net, precision, depth, ring, _validated=_validated)
        finally:
            self._active_contract_calls -= 1
            if self._active_contract_calls == 0:
                for frame in self._frames.values():
                    frame.plans.clear()
                self._frames.clear()
                if self.shared_cache is not None:
                    self.stats.shared_cache_peak_estimated_bytes = max(
                        self.stats.shared_cache_peak_estimated_bytes,
                        self.shared_cache.peak_bytes,
                    )

    def _contract_impl(self, net: Network, precision: int | None = None, depth: int = 0,
                 ring: TensorRing | None = None, *, _validated: bool = False) -> NestedCoords:
        # _validated is trusted only from CompiledChildPlan, whose immutable
        # graph incidence was checked at construction. Public callers validate.
        if not _validated:
            net.validate()
        self.stats.recursive_calls+=1
        self.stats.depth_counts[depth]=self.stats.depth_counts.get(depth,0)+1
        p=self.config.precision if precision is None else precision
        R = Padic(self.e, self.f, p) if ring is None else ring
        if p != R.p:
            raise ValueError('Coefficient-ring precision differs from recursive call')
        r, a, u, H = self.params(depth, net.edges)
        M = net.edges
        # An exact tensor contraction is a valid terminal case at *any*
        # recursive depth. For small children, a bounded leaf is less costly
        # than constructing another nested polynomial coefficient ring.
        # This optional cutoff affects only experimental schedules; the
        # literal paper schedule retains its original stopping conditions.
        if (self.config.schedule != 'paper' and depth > 0 and self.config.leaf.adaptive_limit
                and M <= min(self.config.leaf.adaptive_limit, self.config.leaf.limit)):
            self.stats.adaptive_leaf_cutoffs += 1
            return self._leaf(net, R)
        if M<=H or (self.config.schedule=='paper' and u<1):
            return self._leaf(net, R)
        if not(1<=u<=a) or M<u:
            raise CapacityError('Appendix D active-call inequalities not met')
        if self.config.schedule=='paper':
            Delta=ceil_ninth_tenths(self.config.s)
            if any(len(v.ports)>Delta for v in net.left+net.right):
                raise AssertionError('Input violates degree hypothesis')
            L=1<<a;Darr=r**(2*a)
            if not (M>=2*Darr*Darr*Delta and M>=L*Darr and 2*L<=Delta):
                # Paper explicitly sends finite-size exceptions to the base case.
                return self._leaf(net, R)
        packing = self._prepare_active_packing(net, r, a, u, depth)
        return self._evaluate_and_recover(net, packing, R, depth, u)

    def _prepare_active_packing(
        self, net: Network, r: int, a: int, u: int, depth: int,
    ) -> Packing:
        """Pack one active recursion level; enforce literal paper invariants."""
        L = 1 << a
        packing = pack(
            net, r, a,
            cast(LabelPair | None, self.config.root_labels) if depth == 0 else None,
        )
        audit = audit_packing(net, packing)
        if self.config.schedule=='paper':
            self.stats.active_paper_calls+=1
            if any(len(p.slots)!=L for p in packing.packets):
                raise AssertionError('Packet slot count invariant violated')
            for i in range(u):
                child_audit=child_edge_audit(net,packing,i)
                if not child_audit['exact_port_conservation']:
                    raise AssertionError('Child port conservation violated')
                if not child_audit['paper_shrinkage_satisfied']:
                    raise AssertionError('Child edge-shrinkage invariant violated')
        if self.config.schedule=='paper' and not all(audit[k] for k in (
                'all_edges_packed_exactly_once','orientation_geometry_valid',
                'packet_bound_met','group_load_bound_met')):
            raise AssertionError('Theorem packing invariant violated: '+str(audit))
        self.stats.active_depth_counts[depth]=self.stats.active_depth_counts.get(depth,0)+1
        return packing

    def _evaluate_and_recover(
        self, net: Network, packing: Packing, R: TensorRing,
        depth: int, u: int,
    ) -> NestedCoords:
        """Evaluate exact deformation centers, then recover the contraction."""
        M = net.edges
        a = packing.a
        p = R.p
        L = 1 << a
        h = (3 * M + u - 1) // u
        jets: dict[int, list[NestedCoords]] = {}
        stream: StreamingHermite | None = None
        retained_coefficients = 0
        factor_plan_cache = ValuationCache(
            self.config.recursion.valuation_structures, shared=self.shared_cache)
        try:
            if self.config.recovery.streaming:
                stream = StreamingHermite(M, L, u, R)
            for t in range(-L, L):
                if t == 0:
                    continue
                i = v2(t)
                q = h * max(0, u - i)
                if q == 0:
                    continue
                pt = p + 8 * h * (L // (1 << i)) + 8 * M * (a + 1)
                with (self.cost_ledger.center(t=t, valuation=i, coefficients=q, precision=pt)
                      if self.cost_ledger is not None else nullcontext()) as center_record:
                    if self.config.recovery.method == 'jet':
                        Rp = precision_ring(R, pt)
                    else:
                        Rp = Padic(self.e,self.f,pt)
                    key = (i, pt)
                    if self.config.mode.strategy == 'packet_eliminate':
                        modes: list[Mode] = []
                    else:
                        cached_modes = factor_plan_cache.get_modes(net, packing, i, pt)
                        if cached_modes is None:
                            cached_modes = mode_catalog(
                                net, packing, t, pt, self.config.mode.max_modes,
                                max_catalog_bytes=self.config.limits.max_estimated_bytes)
                            factor_plan_cache.store_modes(net, packing, cached_modes, i, pt)
                            if self.cost_ledger is not None:
                                self.cost_ledger.charge("modes_catalogued", len(cached_modes))
                        modes = cached_modes
                    if self.cost_ledger is not None and center_record is not None:
                        center_record.mode_count = len(modes)
                    if self.config.recovery.method == 'jet':
                        jet = self._jet_center(net, packing, modes, t, Rp, depth, q, factor_plan_cache)
                        if stream is not None:
                            with (self.cost_ledger.phase("recovery") if self.cost_ledger is not None
                                  else nullcontext()):
                                stream.add_center(t, jet)
                            self.stats.streaming_hermite_centers += 1
                            self.stats.retained_jet_coefficients_peak = max(
                                self.stats.retained_jet_coefficients_peak, q)
                        else:
                            jets[t] = list(jet)
                            retained_coefficients += q
                            self.stats.retained_jet_coefficients_peak = max(
                                self.stats.retained_jet_coefficients_peak, retained_coefficients)
                    else:
                        assert isinstance(Rp, Padic)
                        jets[t] = self._interpolated_center(net, packing, modes, t,
                                                            Rp, depth, q, M * (2 * L - 1), factor_plan_cache)
            with (self.cost_ledger.phase("recovery") if self.cost_ledger is not None
                  else nullcontext()):
                if self.config.recovery.method == 'jet':
                    return stream.finish() if stream is not None else tapered_recover_over_ring(jets, M, L, u, R)
                return tapered_recover(cast(Mapping[int, Sequence[RingCoords]], jets), M, L, u, p, self.e, self.f)
        finally:
            factor_plan_cache.clear()

    def _jet_center(
        self, net: Network, packing: Packing, modes: list[Mode],
        t: int, ring: TensorRing, depth: int, order: int,
        factor_plan_cache: ValuationCache | None = None,
    ) -> tuple[NestedCoords, ...]:
        """Evaluate one exact Taylor jet, refusing an oversized coefficient ring."""
        # Inherited Taylor variables remain independent through child calls.
        # Count *all* scalar coordinates before allocating another jet layer.
        coordinates = self.e
        inherited = ring
        while isinstance(inherited, JetRing):
            coordinates *= inherited.q
            inherited = cast(Padic | JetRing, inherited.base)
        required = coordinates * order
        limit = self.config.recovery.max_jet_coordinates
        if required > limit:
            raise CapacityError(
                f'Nested jet needs {required} 2-adic coordinates; budget is {limit}')
        self.stats.max_jet_coordinates = max(self.stats.max_jet_coordinates, required)
        self.stats.max_nested_jet_depth = max(
            self.stats.max_nested_jet_depth, 1 + getattr(ring, 'depth', 0))

        jet_ring = JetRing(ring, order)
        result = cast(tuple[NestedCoords, ...], self.evaluate_deformation(
            net, packing, modes, t, jet_ring.variable, jet_ring, depth,
            factor_plan_cache=factor_plan_cache))
        self.stats.interpolation_evaluations += 1
        if self.cost_ledger is not None:
            self.cost_ledger.charge("deformation_evaluations")
        return result

    def _interpolated_center(
        self, net: Network, packing: Packing, modes: list[Mode],
        t: int, ring: Padic, depth: int, order: int, degree: int,
        factor_plan_cache: ValuationCache | None = None,
    ) -> list[NestedCoords]:
        """Evaluate point samples and retain exactly the required coefficients."""
        samples: list[tuple[RingCoords, RingCoords]] = []
        for z in interp_points(ring, degree + 1):
            value = self.evaluate_deformation(
                net, packing, modes, t, z, ring, depth,
                factor_plan_cache=factor_plan_cache)
            samples.append((z, cast(RingCoords, value)))
            self.stats.interpolation_evaluations += 1
            if self.cost_ledger is not None:
                self.cost_ledger.charge("deformation_evaluations")
        coefficients: list[NestedCoords] = list(interpolate(samples, ring)[:order])
        if len(coefficients) < order:
            coefficients.extend([ring.zero] * (order - len(coefficients)))
        return coefficients
