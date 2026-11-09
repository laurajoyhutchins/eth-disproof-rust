"""Bounded structural reuse across centers of one exact parent contraction.

Only a mode catalog and its topology-dependent factorization plan are held.
No center-dependent packet coefficients, rings or child results are shared.
Entry identity and an immutable mode signature prevent cross-network reuse.
"""
from __future__ import annotations

from dataclasses import dataclass
from sys import getsizeof

from ..core.modes import Mode
from ..core.network import Network
from ..core.packing import Packing
from ..runtime.cache import BudgetedLRU, CachePolicy, SharedCacheBudget
from .planning import FactorizationPlan


@dataclass(frozen=True)
class _Structure:
    net: Network
    packing: Packing
    modes: list[Mode]
    signature: tuple[Mode, ...]
    plan: FactorizationPlan | None = None

    def belongs_to(self, net: Network, packing: Packing,
                   modes: list[Mode]) -> bool:
        return (self.net is net and self.packing is packing
                and self.modes is modes and self.signature == tuple(modes))


def _owned_bytes(entry: _Structure) -> int:
    """Estimate privately retained structures, excluding the shared parent.

    This is an owned-memory estimate, not total RSS or a proof of a byte bound.
    """
    total = getsizeof(entry) + getsizeof(entry.modes) + getsizeof(entry.signature)
    for mode in entry.modes:
        total += (getsizeof(mode) + getsizeof(mode.__dict__)
                  + getsizeof(mode.tile) + getsizeof(mode.rows)
                  + sum(getsizeof(piece) for piece in mode.tile) + 8)
    plan = entry.plan
    if plan is not None:
        total += getsizeof(plan) + getsizeof(plan.factors)
        for spec in plan.factors:
            total += getsizeof(spec) + getsizeof(spec.mode_indices)
            if spec.component is not None:
                component = spec.component
                total += (getsizeof(component) + getsizeof(component.packets)
                          + getsizeof(component.kept)
                          + sum(getsizeof(port) for port in component.kept))
    return max(1, total)


class ValuationCache:
    """Parent-local LRU with optional contraction-wide retained-byte budget.

    Reuse is safe only when network, packing and mode-list identities match.
    Mismatched public calls are cache misses, never foreign-plan applications.
    """

    def __init__(self, policy: CachePolicy,
                 *, shared: SharedCacheBudget | None = None) -> None:
        self.entries: BudgetedLRU[tuple[int, int], _Structure] = BudgetedLRU(
            policy, shared=shared)

    def get_modes(self, net: Network, packing: Packing,
                  coordinate: int, precision: int) -> list[Mode] | None:
        entry = self.entries.get((coordinate, precision))
        if entry is None or entry.net is not net or entry.packing is not packing:
            return None
        if entry.signature != tuple(entry.modes):
            return None
        return entry.modes

    def store_modes(self, net: Network, packing: Packing, modes: list[Mode],
                    coordinate: int, precision: int) -> bool:
        entry = _Structure(net, packing, modes, tuple(modes))
        return self.entries.put((coordinate, precision), entry, _owned_bytes(entry))

    def get_plan(self, net: Network, packing: Packing, modes: list[Mode],
                 coordinate: int, precision: int) -> FactorizationPlan | None:
        entry = self.entries.get((coordinate, precision))
        if entry is None or not entry.belongs_to(net, packing, modes):
            return None
        return entry.plan

    def store_plan(self, net: Network, packing: Packing, modes: list[Mode],
                   coordinate: int, precision: int, plan: FactorizationPlan) -> bool:
        key = (coordinate, precision)
        entry = _Structure(net, packing, modes, tuple(modes), plan)
        return self.entries.put(key, entry, _owned_bytes(entry))

    def clear(self) -> None:
        self.entries.clear()
