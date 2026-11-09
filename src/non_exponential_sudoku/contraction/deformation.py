"""Evaluate one deformation center, by elimination or explicit mode summation.

A center owns its coefficient context and bounded caches. Neither is shared
across interpolation points: only child topology may survive a center.
"""
from __future__ import annotations

from collections import OrderedDict
from contextlib import nullcontext
from typing import TYPE_CHECKING, cast

from ..core.algebra import v2
from ..core.jets import NestedRing
from ..core.lazy_coefficients import NestedCoords
from ..core.modes import Mode, weighted_tuples
from ..core.network import Network, TensorRing
from ..core.packing import Packing
from ..elimination.engine import ModeEliminator
from ..elimination.factors import FactorKey
from ..runtime.budget import CapacityError
from ..runtime.config import ContractorConfig
from ..runtime.cost_ledger import CostLedger, charge
from ..runtime.statistics import Counters
from .admission import estimate_first_factor
from .child_evaluator import ChildEvaluator
from .packets import EvaluationContext
from ..runtime.work_trace import WorkTrace
from .planning import ComponentCapacityExceeded, build_factorization_plan

if TYPE_CHECKING:
    from .engine import ContractionEngine


class DeformationExecution:
    """Per-center evaluation; engine configuration and counters are inherited."""

    stats: Counters
    cost_ledger: CostLedger | None
    work_trace: WorkTrace | None
    config: ContractorConfig

    def evaluate_deformation(
        self, net: Network, packing: Packing, modes: list[Mode], t: int,
        z: NestedCoords, ring: TensorRing, depth: int,
    ) -> NestedCoords:
        with (self.cost_ledger.phase("deformation") if self.cost_ledger is not None
              else nullcontext()):
            return self._evaluate_deformation_impl(net, packing, modes, t, z, ring, depth)

    def _evaluate_deformation_impl(
        self, net: Network, packing: Packing, modes: list[Mode], t: int,
        z: NestedCoords, ring: TensorRing, depth: int,
    ) -> NestedCoords:
        coordinate = v2(t)
        context = EvaluationContext(
            t, z, ring, packing.a,
            packet_coeff_cache_limit=self.config.packets.cache_limit,
            packet_coeff_node_limit=self.config.packets.node_limit,
            packet_coeff_miss_limit=self.config.packets.miss_limit,
            packet_checkpoint_coordinates=self.config.packets.checkpoint_coordinates,
            native_packet=self.config.recursion.native_packet,
            packet_memo_entries=self.config.recursion.packet_memo_entries,
            packet_memo_bytes=self.config.recursion.packet_memo_bytes,
            prepared_packet_entries=self.config.recursion.prepared_packet_entries,
            prepared_packet_bytes=self.config.recursion.prepared_packet_bytes,
            work_trace=self.work_trace,
        )
        occupied = {labels[coordinate] for labels in packing.groups_left + packing.groups_right}
        affected = {
            group: tuple(j for j, mode in enumerate(modes)
                         if mode.source == group or mode.target == group)
            for group in occupied
        }
        try:
            if self.config.mode.strategy == 'eliminate':
                return self._eliminate_modes(
                    net, packing, modes, t, z, ring, depth,
                    coordinate, occupied, affected, context,
                )
            return self._sum_modes(
                net, packing, modes, t, z, ring, depth,
                coordinate, occupied, affected, context,
            )
        finally:
            self._record_packet_statistics(context)

    def _eliminate_modes(
        self, net: Network, packing: Packing, modes: list[Mode], t: int,
        z: NestedCoords, ring: TensorRing, depth: int, coordinate: int,
        occupied: set[int], affected: dict[int, tuple[int, ...]],
        context: EvaluationContext,
    ) -> NestedCoords:
        self.stats.skipped_empty_groups += packing.r - len(occupied)
        try:
            plan = build_factorization_plan(
                net, packing, modes, coordinate, occupied, affected,
                strategy=self.config.mode.factorization,
                max_components=self.config.limits.max_components,
            )
        except ComponentCapacityExceeded as exc:
            # Partial planning statistics remain observable on refusal.
            self.stats.mode_dp_local_arity_before = max(
                self.stats.mode_dp_local_arity_before, exc.before)
            self.stats.mode_dp_max_local_arity_after = max(
                self.stats.mode_dp_max_local_arity_after, exc.after)
            self.stats.mode_dp_local_arity_after += exc.total
            raise CapacityError(str(exc)) from exc

        if self.config.limits.max_child_contractions < self.config.limits.max_factor_states:
            # Only refuse proven mandatory work; runtime guards stay authoritative.
            estimate = estimate_first_factor(
                plan, modes, ring.p,
                max_child_evaluations=self.config.limits.max_child_contractions,
            )
            if estimate.outcome == 'refused':
                raise CapacityError('Mode DP first-factor preflight: ' + estimate.reason)

        self.stats.mode_dp_local_arity_before = max(
            self.stats.mode_dp_local_arity_before, plan.max_arity_before)
        self.stats.mode_dp_max_local_arity_after = max(
            self.stats.mode_dp_max_local_arity_after, plan.max_arity_after)
        self.stats.mode_dp_local_arity_after += plan.total_local_arity_after
        self.stats.mode_dp_split_components += plan.split_components

        child_evaluator = ChildEvaluator(
            cast('ContractionEngine', self), net, packing, modes,
            t, z, ring, depth, coordinate, context,
        )

        def child_for_local_modes(
            factor_key: FactorKey, scope: tuple[int, ...],
            assignment: tuple[int, ...],
        ) -> NestedCoords:
            if plan.factor_scopes is None:
                if not isinstance(factor_key, int):
                    raise AssertionError('Whole-group factor key must be an integer')
                group, component = factor_key, None
            else:
                if not isinstance(factor_key, tuple):
                    raise AssertionError('Component factor key must be a pair')
                group, component = factor_key[0], plan.components[factor_key]
            return child_evaluator.evaluate(
                group, assignment, mode_indices=scope, component=component,
            )

        return ModeEliminator(
            modes, occupied, ring, child_for_local_modes, self.stats, CapacityError,
            factor_scopes=plan.factor_scopes,
            order=self.config.mode.order,
            join_strategy=self.config.mode.join,
            native_sparse=self.config.mode.native_sparse,
            limits=self.config.limits,
        ).run()

    def _sum_modes(
        self, net: Network, packing: Packing, modes: list[Mode], t: int,
        z: NestedCoords, ring: TensorRing, depth: int, coordinate: int,
        occupied: set[int], affected: dict[int, tuple[int, ...]],
        context: EvaluationContext,
    ) -> NestedCoords:
        """Explicit weighted sum, with a bounded center-local child cache."""
        arithmetic = cast(NestedRing, ring)
        result = arithmetic.zero
        child_evaluator = ChildEvaluator(
            cast('ContractionEngine', self), net, packing, modes,
            t, z, ring, depth, coordinate, context,
        )
        child_cache: OrderedDict[tuple[int, tuple[int, ...]], NestedCoords] = OrderedDict()
        cache_limit = 128
        groups = tuple(sorted(occupied))
        for index, assignment in enumerate(weighted_tuples(modes, ring.p)):
            if index >= self.config.mode.max_tuples:
                raise CapacityError('Mode tuple resource limit')
            self.stats.mode_tuples += 1
            charge('mode_tuples_enumerated')
            value = ring.one
            self.stats.skipped_empty_groups += packing.r - len(occupied)
            for group in groups:
                key = (group, tuple(assignment[j] for j in affected[group]))
                if key in child_cache:
                    self.stats.child_cache_hits += 1
                    child_value = child_cache[key]
                    child_cache.move_to_end(key)
                else:
                    child_value = child_evaluator.evaluate(group, assignment)
                    child_cache[key] = child_value
                    if len(child_cache) > cache_limit:
                        child_cache.popitem(last=False)
                value = arithmetic.mul(value, child_value)
                if value == ring.zero:
                    break
            result = arithmetic.add(result, value)
        return result

    def _record_packet_statistics(self, context: EvaluationContext) -> None:
        """Collect a center's metrics even if evaluation refused mid-center."""
        if context.prepared_packets is not None:
            cache = context.prepared_packets
            self.stats.prepared_packet_hits += cache.hits
            self.stats.prepared_packet_misses += cache.misses
            self.stats.prepared_packet_evictions += cache.evictions
            self.stats.prepared_packet_peak_entries = max(
                self.stats.prepared_packet_peak_entries, cache.peak_entries,
            )
            self.stats.prepared_packet_peak_estimated_bytes = max(
                self.stats.prepared_packet_peak_estimated_bytes, cache.peak_bytes,
            )
            self.stats.prepared_packet_oversize_skips += cache.skipped_oversize
            # A prepared packet points back to its center. Break that cycle
            # as soon as the synchronous deformation has completed, rather
            # than retaining coefficient rings until cyclic GC runs.
            cache.clear()
        if context.memo is not None:
            self.stats.packet_entry_memo_hits += context.memo.hits
            self.stats.packet_entry_memo_misses += context.memo.misses
            self.stats.packet_entry_memo_evictions += context.memo.evictions
            self.stats.packet_entry_memo_peak_estimated_bytes = max(
                self.stats.packet_entry_memo_peak_estimated_bytes,
                context.memo.peak_bytes,
            )
        if context.lazy_ring is None:
            return
        lazy = context.lazy_ring
        oracle = lazy.oracle
        self.stats.packet_coefficient_requests += oracle.requests
        self.stats.packet_coefficient_misses += oracle.misses
        self.stats.packet_coefficient_mul_ops += oracle.mul_ops
        self.stats.packet_coefficient_peak_cached = max(
            self.stats.packet_coefficient_peak_cached, oracle.max_cached,
        )
        self.stats.packet_expression_nodes += lazy.nodes
        self.stats.packet_vectors_materialized += lazy.materializations
        self.stats.packet_checkpoint_coordinates += lazy.checkpoint_used
        self.stats.packet_checkpoint_peak_coordinates = max(
            self.stats.packet_checkpoint_peak_coordinates, lazy.checkpoint_used,
        )
        self.stats.packet_checkpoint_count += lazy.checkpoint_count
