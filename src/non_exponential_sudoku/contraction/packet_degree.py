"""Exact zero certificates before constructing an impossible packet child.

The prepared packet tensor extracts one coefficient in target-mode variables
from a product of affine-linear row polynomials. Each row contributes a
total target degree of at most one. If the requested sum of multiplicities
for one packet/group exceeds the number of left rows belonging to that
packet/group, its packet tensor is identically zero, for every Boolean
input and every coefficient ring.

This certificate uses the actual parent packing, never a guessed cost
limit, numerical approximation, or a sampled packet coefficient.
"""
from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass

from ..core.modes import Mode
from ..core.network import Network
from ..core.packing import Packing
from .children import ChildComponent


@dataclass(frozen=True, slots=True)
class PacketDegreeZero:
    packet_id: int
    group: int
    requested_degree: int
    available_rows: int


def packet_target_row_capacity(
    net: Network, packing: Packing, coordinate: int,
) -> dict[tuple[int, int], int]:
    """Count actual Y-row slots by packet and label, once per center."""
    if type(coordinate) is not int or not 0 <= coordinate < packing.a:
        raise ValueError("packet target coordinate is invalid")
    owner = [-1] * net.edges
    for index, vertex in enumerate(net.left):
        for edge in vertex.ports:
            if not 0 <= edge < net.edges or owner[edge] >= 0:
                raise ValueError("invalid parent left incidence for packet capacity")
            owner[edge] = index
    if any(i < 0 for i in owner):
        raise ValueError("parent edge is missing a left endpoint")
    row_counts: dict[tuple[int, int], int] = {}
    for packet_id, packet in enumerate(packing.packets):
        for edge in packet.slots:
            if edge is None:
                continue
            if not 0 <= edge < net.edges:
                raise ValueError("packet contains an invalid parent edge")
            group = packing.groups_left[owner[edge]][coordinate]
            key = (packet_id, group)
            row_counts[key] = row_counts.get(key, 0) + 1
    return row_counts


def impossible_packet_target_degree(
    modes: Sequence[Mode], multiplicities: Sequence[int], *,
    group: int, row_capacity: Mapping[tuple[int, int], int],
    component: ChildComponent | None = None,
) -> PacketDegreeZero | None:
    """Return a sound local certificate, or None when not established.

    Modes that source from this group contribute source-tile powers instead
    of target-mode exponents and are intentionally excluded. Component
    factors only contain their selected packet nodes. The check also
    remains valid when an exact output is zero for additional reasons.

    Invalid mode/multiplicity pairs are not granted a certificate.
    """
    if len(modes) != len(multiplicities):
        raise ValueError("one multiplicity is required per selected mode")
    selected_packets = set(component.packets) if component is not None else None
    demanded: dict[int, int] = {}
    for mode, multiplicity in zip(modes, multiplicities):
        if type(multiplicity) is not int or multiplicity < 0:
            raise ValueError("target mode multiplicities must be nonnegative integers")
        if multiplicity == 0 or mode.target != group:
            continue
        if selected_packets is not None and mode.packet not in selected_packets:
            continue
        if mode.packet < 0:
            return None
        total = demanded.get(mode.packet, 0) + multiplicity
        demanded[mode.packet] = total
        available = row_capacity.get((mode.packet, group))
        if available is None:
            # A corrupt or foreign packet ID must be rejected by the
            # constructor rather than misclassified as a proof of zero.
            return None
        if total > available:
            return PacketDegreeZero(mode.packet, group, total, available)
    return None
