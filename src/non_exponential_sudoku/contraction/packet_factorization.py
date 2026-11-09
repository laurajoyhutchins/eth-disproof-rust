"""Exact direct contraction of packet-deformed Boolean tensors.

For every original edge e introduce *two* Boolean wires Y_e and X_e.
Move both original vertex families to the left of a bipartite factor
network, and attach one packet tensor on the right for all Y/X ports
owned by that packet. No weighted mode descriptor or child contraction
is needed: the factor graph represents exactly the same polynomial F.

This is an experimental width-bounded reordering, not an implementation
of the paper's recursive subexponential schedule. The width and factor
memory preflights fail closed before evaluating any vertex oracle.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import cast

from ..core.lazy_coefficients import NestedCoords
from ..core.jets import NestedRing
from ..core.network import (
    LeafPlan, Network, TensorRing, Vertex, compile_leaf_plan, eliminate_leaf,
)
from ..core.packing import Packing
from ..runtime.budget import CapacityError
from .packets import PacketRing, cauchy_values


def _unbound_packet(_bits: tuple[int, ...], _ring: TensorRing) -> NestedCoords:
    raise RuntimeError("Packet-factor topology must be bound to a deformation center")


@dataclass(frozen=True)
class PacketFactorPlan:
    """Topology only; packet factors are bound at evaluation time."""

    network: Network
    leaf_plan: LeafPlan
    slots: tuple[tuple[tuple[int, int], ...], ...]
    max_width: int


def compile_packet_deformation(
    net: Network, packing: Packing, *, max_width: int = 16,
) -> PacketFactorPlan:
    """Preflight an exact width-bounded lifted factor graph.

    Each original wire appears once as a Y wire and once as an X wire.
    The packet tensors consume both, and the original vertex oracles
    are carried over unchanged. No factor values are evaluated here.
    """
    if max_width < 1:
        raise ValueError("Packet elimination width must be positive")
    net.validate()
    width = 2 * net.edges
    left = [
        Vertex(v.name, tuple(2*e for e in v.ports), v.oracle)
        for v in net.left
    ] + [
        Vertex(v.name, tuple(2*e+1 for e in v.ports), v.oracle)
        for v in net.right
    ]
    right: list[Vertex] = []
    sites: list[tuple[tuple[int, int], ...]] = []
    edge_counts = [0] * net.edges
    for k, packet in enumerate(packing.packets):
        if len(packet.slots) != 1 << packing.a:
            raise ValueError("Packet slot count does not match exponent")
        occupied: list[tuple[int, int]] = []
        for slot, edge in enumerate(packet.slots):
            if edge is not None:
                if edge < 0 or edge >= net.edges:
                    raise ValueError("Packet references an invalid wire")
                edge_counts[edge] += 1
                occupied.append((slot, edge))
        sites.append(tuple(occupied))
        ports = (
            tuple(2*e for _, e in occupied) +
            tuple(2*e+1 for _, e in occupied)
        )
        right.append(Vertex(f"packet:{k}", ports, _unbound_packet))
    if any(n != 1 for n in edge_counts):
        raise ValueError("Packet partition must contain each wire exactly once")
    lifted = Network(left, right, width)
    lifted.validate()
    scopes = tuple(v.ports for v in lifted.left + lifted.right)
    plan = compile_leaf_plan(width, scopes, max_width=max_width)
    if plan is None:
        raise CapacityError("Lifted packet deformation exceeds factor width limit")
    return PacketFactorPlan(lifted, plan, tuple(sites), max_width)


@dataclass(frozen=True)
class _BoundPacket:
    """One exact packet factor, using weights shared across the center."""

    occupied: tuple[tuple[int, int], ...]
    weights: dict[int, NestedCoords]
    ring: TensorRing

    def __call__(self, bits: tuple[int, ...], supplied_ring: TensorRing) -> NestedCoords:
        if supplied_ring is not self.ring:
            raise ValueError("Packet factor was bound to a different coefficient ring")
        n = len(self.occupied)
        if len(bits) != 2*n:
            raise ValueError("Packet factor requires Y and X assignments")
        R = cast(NestedRing, supplied_ring)
        result = R.one
        for row, (x, _) in enumerate(self.occupied):
            wx = R.zero
            for col, (y, _) in enumerate(self.occupied):
                if bits[n + col]:
                    wx = R.add(wx, self.weights[y-x])
            factor = wx if bits[row] else R.sub(R.one, wx)
            result = R.mul(result, factor)
            if result == R.zero:
                break
        return result


def evaluate_packet_deformation(
    net: Network, packing: Packing, t: int, z: NestedCoords,
    ring: TensorRing, *, max_width: int = 16,
    max_factor_bytes: int = 128*1024*1024,
) -> NestedCoords:
    """Evaluate the same F(t+2L*z) without summing mode assignments.

    The result is exact modulo the coefficient ring's precision. All
    allocation and width controls come from the existing leaf policy;
    no fallback to exponential direct enumeration is permitted.
    """
    if max_factor_bytes < 1:
        raise ValueError("Packet factor memory budget must be positive")
    # Rebuild the structural plan for these exact inputs. Reusing a plan
    # from a different packet partition would silently change the answer;
    # a validated exact-plan cache may be introduced only with proof of
    # full network and packing identity.
    plan = compile_packet_deformation(net, packing, max_width=max_width)
    # Packet factors share one Cauchy kernel and differ only by slot labels.
    weights = cast(dict[int, NestedCoords], cauchy_values(
        t, z, cast(PacketRing, ring), 1 << packing.a,
    ))
    right = [
        Vertex(v.name, v.ports, _BoundPacket(sites, weights, ring))
        for v, sites in zip(plan.network.right, plan.slots)
    ]
    lifted = Network(plan.network.left, right, plan.network.edges)
    return eliminate_leaf(
        lifted, ring, max_edges=0, max_width=max_width,
        plan=plan.leaf_plan, max_factor_bytes=max_factor_bytes,
    )
