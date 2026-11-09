from __future__ import annotations

from dataclasses import dataclass
from collections import defaultdict
from itertools import product
from typing import TypedDict, TypeAlias, TYPE_CHECKING
from ..core.modes import Mode
from ..core.network import TensorRing
from ..core.lazy_coefficients import NestedCoords
from .packets import EvaluationContext
from ..core.network import Network, Vertex
from ..core.packing import Packing
from .packets import PacketEntry
if TYPE_CHECKING:
    from .compiled_children import CompiledChildPlan
from ..core.algebra import v2

_Node: TypeAlias = int
class _ChildPart(TypedDict):
    kept: list[tuple[str, int]]
    packets: set[int]

class ChildEdgeAudit(TypedDict):
    edges_by_group: tuple[int, ...]
    total_child_edges: int
    max_child_edges: int
    paper_shrinkage_satisfied: bool
    exact_port_conservation: bool

@dataclass(frozen=True)
class ChildComponent:
    """Connected component of a child graph, independent of mode values.

    `kept` contains parent-side vertices, `packets` the packet tensors.
    Every mode incident to this group belongs to precisely one component,
    determined by its packet.  Empty, unconnected packet tensors are one:
    they have no bits and no incident modes, so they may be omitted exactly.
    """
    packets: tuple[int, ...]
    kept: tuple[tuple[str, int], ...]


def child_components(net: Network, packing: Packing, group: int, coordinate: int) -> tuple[ChildComponent, ...]:
    """Exact connected-component partition of the *topology* of make_child.

    The parent vertices and packet nodes form a bipartite incidence graph.
    Its topology is independent of Cauchy parameters and mode multiplicities.
    We omit only packet nodes with zero incident child ports, whose entries
    are identically one for this group (no mode may target/source such a node).
    """
    packet_count = len(packing.packets)
    packet_for_edge = {edge: k for k, packet in enumerate(packing.packets)
                       for edge in packet.slots if edge is not None}
    parent: dict[_Node, _Node] = {}
    def find(x: _Node) -> _Node:
        parent.setdefault(x, x)
        if parent[x] != x: parent[x] = find(parent[x])
        return parent[x]
    def union(a: _Node, b: _Node) -> None:
        a, b = find(a), find(b)
        if a != b: parent[b] = a
    kept: list[tuple[_Node, tuple[str, int]]] = []
    for side, vertices, labels in (('Y', net.left, packing.groups_left),
                                   ('X', net.right, packing.groups_right)):
        for j, vertex in enumerate(vertices):
            if labels[j][coordinate] != group: continue
            # Disjoint numeric namespaces: packets, left vertices, right vertices.
            node = packet_count + j + (len(net.left) if side == 'X' else 0)
            find(node)
            kept.append((node, (side, j)))
            for edge in vertex.ports:
                union(node, packet_for_edge[edge])
    parts: dict[_Node, _ChildPart] = {}
    for kept_node, label in kept:
        target = parts.setdefault(find(kept_node), {'kept': [], 'packets': set()})
        target['kept'].append(label)
    for packet_node in tuple(parent):
        if packet_node < packet_count:
            target = parts.setdefault(find(packet_node), {'kept': [], 'packets': set()})
            target['packets'].add(packet_node)
    result = [ChildComponent(tuple(sorted(part['packets'])), tuple(part['kept']))
              for part in parts.values()]
    result.sort(key=lambda part: (part.packets[0] if part.packets else len(packing.packets), part.kept))
    return tuple(result)


def compile_child(net: Network, packing: Packing, group: int, i: int,
                  component: ChildComponent | None = None) -> CompiledChildPlan:
    """Reuse v20's validated compiled topology, not a parallel plan type."""
    from .compiled_children import CompiledChildPlan
    return CompiledChildPlan(net,packing,group,i,component)


def make_child(net: Network, packing: Packing, modes: list[Mode], beta: tuple[int, ...],
               t: int, z: NestedCoords, R: TensorRing, group: int, i: int,
               context: EvaluationContext | None = None,
               component: ChildComponent | None = None,
               *, plan: CompiledChildPlan | None = None) -> Network:
    if plan is not None:
        if (plan.net is not net or plan.packing is not packing or
                plan.group!=group or plan.coordinate!=i or plan.component!=component):
            raise ValueError('Compiled child plan does not match requested network')
        return plan.instantiate(modes,beta,t,z,R,context) if context is not None else \
            plan.instantiate(modes,beta,t,z,R,EvaluationContext(t,z,R,packing.a))
    left: list[Vertex] = []; right: list[Vertex] = []
    port_locations: defaultdict[int, list[tuple[str, int, int]]] = defaultdict(list)
    next_edge=0
    owners_l={e:j for j,v in enumerate(net.left) for e in v.ports}
    owners_r={e:j for j,v in enumerate(net.right) for e in v.ports}
    packet_for_edge={e:k for k,pkt in enumerate(packing.packets) for e in pkt.slots if e is not None}
    slot_for_edge={e:x for pkt in packing.packets for x,e in enumerate(pkt.slots) if e is not None}
    selected_kept = set(component.kept) if component is not None else None
    selected_packets = set(component.packets) if component is not None else None
    for side,verts,labels in (('Y',net.left,packing.groups_left),('X',net.right,packing.groups_right)):
        for j,vert in enumerate(verts):
            if labels[j][i]!=group or (selected_kept is not None and (side,j) not in selected_kept): continue
            child_edges=[]
            for edge in vert.ports:
                child_edges.append(next_edge)
                packet_idx=packet_for_edge[edge];slot=slot_for_edge[edge]
                port_locations[packet_idx].append((side,slot,next_edge))
                next_edge+=1
            # Names are diagnostic, not graph identity. Preserve the source label
            # rather than recursively prefixing it at every contraction depth.
            left.append(Vertex(vert.name,tuple(child_edges),vert.oracle))
    for k,pkt in enumerate(packing.packets):
        if selected_packets is not None and k not in selected_packets: continue
        mapping=port_locations[k]
        port_map={(side,slot):j for j,(side,slot,_) in enumerate(mapping)}
        entry=PacketEntry(net,packing,k,group,i,t,z,R,modes,beta,port_map,context)
        right.append(Vertex(f'packet:{k}:g{group}',tuple(edge for _,_,edge in mapping),entry))
    child=Network(left,right,next_edge)
    child.validate()
    return child


def child_edge_audit(net:Network, packing:Packing, coordinate:int) -> ChildEdgeAudit:
    """Count retained child wires without enumerating mode tuples.

    An edge contributes one retained port from each endpoint, hence the
    total across all groups is exactly 2M, irrespective of beta or z.
    """
    loads=[0]*packing.r
    for vertex,label in zip(net.left,packing.groups_left):
        loads[label[coordinate]] += len(vertex.ports)
    for vertex,label in zip(net.right,packing.groups_right):
        loads[label[coordinate]] += len(vertex.ports)
    return {
        'edges_by_group':tuple(loads),
        'total_child_edges':sum(loads),
        'max_child_edges':max(loads,default=0),
        'paper_shrinkage_satisfied':all(32*m<=3*net.edges for m in loads),
        'exact_port_conservation':sum(loads)==2*net.edges,
    }


def ceil_ninth_tenths(n:int) -> int:
    """Exact ceil(n**(9/10)) with integer comparisons; no float overflow."""
    if n<1:raise ValueError('expected positive n')
    target=n**9
    low=0; high=1<<((target.bit_length()+9)//10)
    while low+1<high:
        mid=(low+high)//2
        if mid**10<target:low=mid
        else:high=mid
    return high
