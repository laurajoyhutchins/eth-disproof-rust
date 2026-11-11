"""Conservative support views for *unbuilt* recursive child factors.

A support view shares validated compiled topology and parent oracles, but
creates no PacketEntry, Cauchy coefficient or p-adic packet arithmetic.
Every retained support assignment overapproximates the exact tensor support.
Binary arc consistency can therefore prove zero before charging a child.

The view caches only local Boolean support of *kept parent vertices* at one
coefficient ring and center. Packet constraints remain dependent on mode
multiplicity and are rebuilt from integer masks for each candidate.
"""
from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from sys import getsizeof

from ..core.modes import Mode
from ..core.network import TensorRing
from ..runtime.config import ZeroSupportPolicy
from .compiled_children import CompiledChildPlan, PacketPorts
from .zero_support import (
    ZeroSupportResult, propagate_support_tables,
)

SupportTable = tuple[tuple[int, ...], tuple[int, ...]]


@dataclass(frozen=True, slots=True)
class _PacketSupport:
    """Necessary Boolean support conditions, expressed as bit masks."""

    source_masks: tuple[int, ...]
    no_target_rows: tuple[tuple[int, int], ...]
    impossible_target: bool = False

    def possible(self, mask: int) -> bool:
        if self.impossible_target:
            return False
        if any(not (mask & required) for required in self.source_masks):
            return False
        if any(mask & left and not (mask & right)
               for left, right in self.no_target_rows):
            return False
        return True


def _packet_support(spec: PacketPorts, active: Sequence[tuple[Mode, int]],
                    group: int) -> _PacketSupport:
    source_masks: list[int] = []
    targets: list[tuple[Mode, int]] = []
    for mode, count in active:
        if mode.source == group:
            mask = 0
            for edge, coefficient in mode.tile:
                pos = spec.geometry.port_map.get(
                    ('X', spec.geometry.slot_for_edge[edge]))
                if pos is not None and (mode.b == 0 or coefficient != 0):
                    mask |= 1 << pos
            source_masks.append(mask)
        if mode.target == group:
            targets.append((mode, count))
    # Each target exponent requires one *distinct* row contribution. Any
    # sum of multiplicities exceeding the available rows vanishes exactly.
    infeasible = (sum(count for _, count in targets) > len(spec.rows)
                  or any(count > sum(row in mode.rows for row in spec.rows)
                         for mode, count in targets))
    constraints = () if targets else tuple(
        (1 << left, sum(1 << pos for pos, _ in right))
        for _, left, right in spec.geometry.row_terms)
    return _PacketSupport(tuple(source_masks), constraints, infeasible)


@dataclass(frozen=True, slots=True)
class PreparedFactorSupport:
    """Ring-local parent support, never inherited across different centers."""

    plan: CompiledChildPlan
    kept: tuple[SupportTable, ...]
    kept_evaluations: int
    impossible_kept: bool

    def estimated_owned_bytes(self) -> int:
        return (256 + getsizeof(self.kept) + sum(
            getsizeof(ports) + getsizeof(table) +
            sum(getsizeof(row) for row in table)
            for ports, table in self.kept))

    def certify(self, modes: Sequence[Mode], beta: Sequence[int],
                policy: ZeroSupportPolicy) -> ZeroSupportResult:
        if len(modes) != len(beta):
            raise ValueError('Pre-factor support needs one multiplicity per mode')
        if len(modes) > policy.max_mode_terms:
            return ZeroSupportResult('unsupported', 0)
        if self.impossible_kept:
            return ZeroSupportResult('zero', 0)
        active: dict[int, list[tuple[Mode, int]]] = {}
        for mode, count in zip(modes, beta):
            if count > 0:
                active.setdefault(mode.packet, []).append((mode, count))
        factors = list(self.kept)
        evaluated = 0
        for spec in self.plan.packet_ports:
            support = _packet_support(
                spec, active.get(spec.packet_id, ()), self.plan.group)
            if support.impossible_target or 0 in support.source_masks:
                return ZeroSupportResult('zero', evaluated)
            possible: list[int] = []
            for mask in range(1 << len(spec.edges)):
                evaluated += 1
                if support.possible(mask):
                    possible.append(mask)
            if not possible:
                return ZeroSupportResult('zero', evaluated)
            factors.append((spec.edges, tuple(possible)))
        return propagate_support_tables(self.plan.edges, tuple(factors), evaluated)


def prepare_factor_support(
    plan: CompiledChildPlan, ring: TensorRing, policy: ZeroSupportPolicy,
) -> PreparedFactorSupport | None:
    """Admit *all* support tables before calling any parent oracle.

    Returning None is a resource refusal, not a zero certificate.
    """
    if plan.edges > policy.max_child_edges:
        return None
    rows = 0
    for ports in (tuple(v.ports for v in plan.kept) +
                  tuple(spec.edges for spec in plan.packet_ports)):
        arity = len(ports)
        if arity > policy.max_vertex_arity:
            return None
        rows += 1 << arity
        if rows > policy.max_support_rows:
            return None
    kept: list[SupportTable] = []
    evaluations = 0
    for vertex in plan.kept:
        table: list[int] = []
        for mask in range(1 << len(vertex.ports)):
            bits = tuple((mask >> j) & 1 for j in range(len(vertex.ports)))
            evaluations += 1
            if vertex.oracle(bits, ring) != ring.zero:
                table.append(mask)
        if not table:
            return PreparedFactorSupport(plan, tuple(kept), evaluations, True)
        kept.append((vertex.ports, tuple(table)))
    return PreparedFactorSupport(plan, tuple(kept), evaluations, False)


def certify_pre_factor_zero(
    plan: CompiledChildPlan, modes: Sequence[Mode], beta: Sequence[int],
    ring: TensorRing, policy: ZeroSupportPolicy,
) -> ZeroSupportResult:
    """Standalone check; callers may cache the prepared view per center."""
    if len(modes) != len(beta):
        raise ValueError('Pre-factor support needs one multiplicity per mode')
    prepared = prepare_factor_support(plan, ring, policy)
    if prepared is None:
        return ZeroSupportResult('unsupported', 0)
    result = prepared.certify(modes, beta, policy)
    return ZeroSupportResult(result.verdict,
                             result.evaluated_rows + prepared.kept_evaluations)
