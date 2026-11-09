"""Exact, bounded zero certificates for child tensor contractions.

Each vertex's nonzero Boolean support is overapproximated. Arc consistency
only removes impossible edge values. If a factor has no supported assignment,
every complete tensor assignment has a zero factor, so contraction is exactly
zero over any coefficient ring. No branching or approximate arithmetic.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from ..core.network import Network, TensorRing
from ..runtime.config import ZeroSupportPolicy
from .packets import PacketEntry


@dataclass(frozen=True)
class ZeroSupportResult:
    verdict: Literal['zero', 'possible', 'unsupported']
    evaluated_rows: int


def _packet_may_be_nonzero(packet: PacketEntry, bits: tuple[int, ...]) -> bool:
    """Conservative support without constructing p-adic coefficients.

    A positive-power source tile vanishes when its selected integer-weight
    sum is zero. Without target multiplicities, Y=1 and no selected X forces
    its row Cauchy factor to zero. All other inputs remain possibly nonzero,
    including any coefficient cancellations not proven structurally.
    """
    for mode, multiplicity, tile in packet.terms.tile_bits:
        if multiplicity > 0 and mode.b >= 0 and not sum(
            j ** mode.b for pos, j in tile if bits[pos]
        ):
            return False
    if not packet.terms.desired:
        for _, left_pos, right_terms in packet.geometry.row_terms:
            if bits[left_pos] and not any(bits[pos] for pos, _ in right_terms):
                return False
    return True


def certify_zero(
    net: Network, ring: TensorRing, policy: ZeroSupportPolicy,
) -> ZeroSupportResult:
    """Return a certificate, an inconclusive result, or a bounded refusal.

    Ordinary vertex support is evaluated in the actual coefficient ring.
    Packet support uses a proven overapproximation only; it never projects
    coefficients into a smaller modulus. The table budget is checked *before*
    any tensor oracle is evaluated. Inconclusive always executes the child.
    """
    if net.edges > policy.max_child_edges:
        return ZeroSupportResult('unsupported', 0)
    vertices = net.left + net.right
    rows = 0
    for vertex in vertices:
        arity = len(vertex.ports)
        if arity > policy.max_vertex_arity:
            return ZeroSupportResult('unsupported', 0)
        rows += 1 << arity
        if rows > policy.max_support_rows:
            return ZeroSupportResult('unsupported', 0)

    tables: list[tuple[int, ...]] = []
    evaluated = 0
    for vertex in vertices:
        possible_assignments: list[int] = []
        oracle = vertex.oracle
        for assignment in range(1 << len(vertex.ports)):
            bits = tuple((assignment >> i) & 1 for i in range(len(vertex.ports)))
            evaluated += 1
            possible = (
                _packet_may_be_nonzero(oracle, bits)
                if isinstance(oracle, PacketEntry)
                else oracle(bits, ring) != ring.zero
            )
            if possible:
                possible_assignments.append(assignment)
        if not possible_assignments:
            return ZeroSupportResult('zero', evaluated)
        tables.append(tuple(possible_assignments))

    domains = [3] * net.edges  # 1 = permit zero; 2 = permit one
    # Every changing pass removes an edge/bit possibility, at most 2M.
    for _ in range(2 * net.edges + 1):
        changed = False
        for vertex, candidates in zip(vertices, tables):
            local_support = [0] * len(vertex.ports)
            compatible = False
            for assignment in candidates:
                if any(
                    not (domains[edge] & (1 << ((assignment >> j) & 1)))
                    for j, edge in enumerate(vertex.ports)
                ):
                    continue
                compatible = True
                for j in range(len(vertex.ports)):
                    local_support[j] |= 1 << ((assignment >> j) & 1)
            if not compatible:
                return ZeroSupportResult('zero', evaluated)
            for edge, mask in zip(vertex.ports, local_support):
                narrower = domains[edge] & mask
                if narrower == 0:
                    return ZeroSupportResult('zero', evaluated)
                if narrower != domains[edge]:
                    domains[edge] = narrower
                    changed = True
        if not changed:
            return ZeroSupportResult('possible', evaluated)
    raise AssertionError('Binary arc consistency failed to converge')
