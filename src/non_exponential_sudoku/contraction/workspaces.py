"""Depth-scoped, bounded structural workspaces for recursive contractions.

Frames hold topology only, not exact coefficient values. A frame at depth d
is never overwritten while a call at depth d is suspended: descendants use
d+1. The parent identity is checked with `is`, not a mutable network hash.
"""
from __future__ import annotations
from collections import OrderedDict
from ..core.network import Network
from ..core.packing import Packing
from .children import ChildComponent
from .compiled_children import CompiledChildPlan


class FrameWorkspace:
    __slots__=('net','packing','plans','edge_to_packet','edge_to_slot','left_owner','max_plans')

    def __init__(self, max_plans: int = 64) -> None:
        self.net: Network | None = None
        self.packing: Packing | None = None
        self.plans: OrderedDict[tuple[int, int, ChildComponent | None], CompiledChildPlan] = OrderedDict()
        self.edge_to_packet: dict[int, int] = {}
        self.edge_to_slot: dict[int, int] = {}
        self.left_owner: dict[int, int] = {}
        self.max_plans=max_plans

    def _set_parent(self, net: Network, packing: Packing) -> None:
        if self.net is net and self.packing is packing:
            return
        self.net=net
        self.packing=packing
        self.plans.clear()
        self.edge_to_packet={e:k for k,p in enumerate(packing.packets)
                             for e in p.slots if e is not None}
        self.edge_to_slot={e:x for p in packing.packets
                           for x,e in enumerate(p.slots) if e is not None}
        self.left_owner={e:j for j,v in enumerate(net.left) for e in v.ports}

    def get_plan(self, net: Network, packing: Packing, group: int, coordinate: int,
                 component: ChildComponent | None) -> tuple[CompiledChildPlan, bool]:
        self._set_parent(net,packing)
        key=(group,coordinate,component)
        plan=self.plans.get(key)
        if plan is not None:
            self.plans.move_to_end(key)
            return plan, True
        plan=CompiledChildPlan(net,packing,group,coordinate,component,
                  self.edge_to_packet,self.edge_to_slot,self.left_owner)
        self.plans[key]=plan
        if len(self.plans)>self.max_plans:
            self.plans.popitem(last=False)
        return plan, False
