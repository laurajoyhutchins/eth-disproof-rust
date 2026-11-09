"""Validated, reusable topology of a recursive child contraction.

Only topology is compiled across centers. Prepared packet oracles may be
reused *within one center* when their exact active modes agree, but child
results and arbitrary parent oracles are never memoized by this plan.
The constructor validates incidence once; instantiation changes only oracles.
"""
from __future__ import annotations

from dataclasses import dataclass
from collections.abc import Mapping
from types import MappingProxyType
from ..core.packing import Packing
from ..core.modes import Mode
from ..core.lazy_coefficients import NestedCoords
from ..core.network import TensorRing
from .children import ChildComponent
from .packets import EvaluationContext
from ..core.network import Network, Vertex
from .packets import PacketEntry, PacketGeometry, prepare_packet_geometry


@dataclass(frozen=True)
class PacketPorts:
    packet_id: int
    edges: tuple[int, ...]
    port_map: Mapping[tuple[str, int], int]
    rows: tuple[int, ...]
    geometry: PacketGeometry

    def __post_init__(self) -> None:
        object.__setattr__(self, "port_map", MappingProxyType(dict(self.port_map)))


class CompiledChildPlan:
    __slots__ = ('net','packing','group','coordinate','component','kept','packet_ports','edges','leaf_plan')

    def __init__(self, net: Network, packing: Packing, group: int, coordinate: int,
                 component: ChildComponent | None = None,
                 edge_to_packet: dict[int, int] | None = None,
                 edge_to_slot: dict[int, int] | None = None,
                 left_owner: dict[int, int] | None = None) -> None:
        self.net=net
        self.packing=packing
        self.group=group
        self.coordinate=coordinate
        self.component=component
        if edge_to_packet is None:
            edge_to_packet={e:k for k,p in enumerate(packing.packets)
                            for e in p.slots if e is not None}
        if edge_to_slot is None:
            edge_to_slot={e:x for p in packing.packets
                          for x,e in enumerate(p.slots) if e is not None}
        if left_owner is None:
            left_owner={e:j for j,v in enumerate(net.left) for e in v.ports}
        selected_kept=set(component.kept) if component is not None else None
        selected_packets=set(component.packets) if component is not None else None
        kept=[]
        locations: dict[int, list[tuple[str, int, int]]] = {}
        n=0
        for side,vertices,labels in (('Y',net.left,packing.groups_left),
                                     ('X',net.right,packing.groups_right)):
            for j,v in enumerate(vertices):
                if labels[j][coordinate]!=group or (selected_kept is not None and (side,j) not in selected_kept):
                    continue
                ports=tuple(range(n,n+len(v.ports)))
                for edge,child_edge in zip(v.ports,ports):
                    k=edge_to_packet[edge]
                    locations.setdefault(k,[]).append((side,edge_to_slot[edge],child_edge))
                n+=len(ports)
                kept.append(Vertex('keep:'+v.name,ports,v.oracle))
        packet_ports=[]
        for k,p in enumerate(packing.packets):
            if selected_packets is not None and k not in selected_packets:
                continue
            mapping=locations.get(k,())
            port_map={(side,slot):j for j,(side,slot,_) in enumerate(mapping)}
            geometry=prepare_packet_geometry(packing,k,group,coordinate,
                                             port_map,left_owner)
            packet_ports.append(PacketPorts(k,tuple(edge for _,_,edge in mapping),
                                            port_map,geometry.rows,geometry))
        # No child mutates this list; it is shared across sibling Network
        # views, avoiding another list allocation per mode assignment.
        self.kept=kept
        self.packet_ports=tuple(packet_ports)
        self.edges=n
        # Computed once per structural child plan; does not retain ring values.
        from ..core.network import compile_leaf_plan
        scopes=tuple(v.ports for v in kept) + tuple(spec.edges for spec in packet_ports)
        self.leaf_plan=compile_leaf_plan(n,scopes) if n<=20 else None
        # Validate once, independently of packet values. Every edge is owned
        # by precisely one kept vertex and precisely one packet tensor.
        left=[0]*n;right=[0]*n
        for v in kept:
            for edge in v.ports:left[edge]+=1
        for spec in packet_ports:
            for edge in spec.edges:right[edge]+=1
        if any(x!=1 for x in left+right):
            raise AssertionError('Invalid compiled child incidence')

    def instantiate(self, modes: list[Mode], beta: tuple[int, ...], t: int,
                    z: NestedCoords, R: TensorRing, context: EvaluationContext) -> Network:
        if len(modes) != len(beta):
            raise ValueError(
                f"Compiled child requires one multiplicity per mode: "
                f"{len(modes)} modes, {len(beta)} multiplicities"
            )
        right=[]
        for spec in self.packet_ports:
            cache = context.prepared_packets
            # Only modes active in *this packet* influence its coefficients.
            # The topology, ring and center are captured in the remaining key
            # fields; unrelated modes can safely share this prepared oracle.
            if cache is not None:
                key: tuple[object, ...] = (
                    id(spec.geometry), spec.packet_id, self.group,
                    self.coordinate, t, id(z), id(R),
                    tuple((mode, multiplicity) for mode, multiplicity
                          in zip(modes, beta)
                          if mode.packet == spec.packet_id and multiplicity > 0),
                )
                oracle = cache.get(key)
            else:
                oracle = None
            if oracle is None:
                oracle = PacketEntry(
                    self.net, self.packing, spec.packet_id, self.group,
                    self.coordinate, t, z, R, modes, beta,
                    spec.port_map, context, prepared_rows=spec.rows,
                    geometry=spec.geometry,
                )
                if cache is not None:
                    cache.put(key, oracle)
            right.append(Vertex(f'packet:{spec.packet_id}:g{self.group}',spec.edges,oracle))
        return Network(self.kept,right,self.edges,leaf_plan=self.leaf_plan)
