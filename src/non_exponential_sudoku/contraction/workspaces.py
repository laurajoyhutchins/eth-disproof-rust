"""Depth-scoped structural workspaces with explicit retention budgets.

Frames hold topology only, not exact coefficient values. A depth-d frame is
never overwritten while its call is suspended: descendants use depth d+1.
Cache entries retain only plan-owned structures, not ring coefficients.
"""
from __future__ import annotations

from sys import getsizeof
from ..core.network import Network
from ..core.packing import Packing
from ..runtime.cache import BudgetedLRU, CachePolicy
from ..runtime.config import LeafConfig
from .children import ChildComponent
from .compiled_children import CompiledChildPlan


def _plan_owned_bytes(plan: CompiledChildPlan) -> int:
    """Estimate owned plan structure, excluding shared net/packing/oracles."""
    total = 512 + getsizeof(plan.kept) + getsizeof(plan.packet_ports)
    for kept in plan.kept:
        total += getsizeof(kept) + getsizeof(kept.ports) + 16 * len(kept.ports)
    for entry in plan.packet_ports:
        total += (256 + getsizeof(entry) + getsizeof(entry.edges) +
                  getsizeof(entry.port_map) + getsizeof(entry.rows) +
                  96 * len(entry.port_map) + 16 * len(entry.rows))
    if plan.leaf_plan is not None:
        total += 256 + getsizeof(plan.leaf_plan.steps)
        for step in plan.leaf_plan.steps:
            total += (256 + getsizeof(step) + getsizeof(step.incident) +
                      getsizeof(step.out_scope) + getsizeof(step.positions))
            if step.lookup is not None:
                total += getsizeof(step.lookup)
                for row in step.lookup:
                    total += getsizeof(row) + 64 * len(row)
    return total


class FrameWorkspace:
    __slots__ = (
        'net', 'packing', 'plans', 'edge_to_packet', 'edge_to_slot',
        'left_owner', 'leaf',
    )

    def __init__(
        self, max_plans: int = 64, *,
        cache_policy: CachePolicy | None = None,
        leaf: LeafConfig | None = None,
    ) -> None:
        if max_plans < 0:
            raise ValueError('Plan entry limit must be nonnegative')
        self.net: Network | None = None
        self.packing: Packing | None = None
        policy = cache_policy or CachePolicy(max_bytes=8 * 1024 * 1024,
                                             max_entries=max_plans)
        self.plans: BudgetedLRU[
            tuple[int, int, ChildComponent | None], CompiledChildPlan
        ] = BudgetedLRU(policy)
        self.edge_to_packet: dict[int, int] = {}
        self.edge_to_slot: dict[int, int] = {}
        self.left_owner: dict[int, int] = {}
        self.leaf = LeafConfig() if leaf is None else leaf

    def _set_parent(self, net: Network, packing: Packing) -> None:
        if self.net is net and self.packing is packing:
            return
        self.net = net
        self.packing = packing
        self.plans.clear()
        self.edge_to_packet = {e: k for k, p in enumerate(packing.packets)
                               for e in p.slots if e is not None}
        self.edge_to_slot = {e: x for p in packing.packets
                             for x, e in enumerate(p.slots) if e is not None}
        self.left_owner = {e: j for j, v in enumerate(net.left) for e in v.ports}

    def get_plan(
        self, net: Network, packing: Packing, group: int, coordinate: int,
        component: ChildComponent | None,
    ) -> tuple[CompiledChildPlan, bool]:
        self._set_parent(net, packing)
        key = (group, coordinate, component)
        plan = self.plans.get(key)
        if plan is not None:
            return plan, True
        plan = CompiledChildPlan(
            net, packing, group, coordinate, component,
            self.edge_to_packet, self.edge_to_slot, self.left_owner,
            leaf=self.leaf,
        )
        self.plans.put(key, plan, _plan_owned_bytes(plan))
        return plan, False
