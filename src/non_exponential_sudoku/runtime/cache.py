"""Bounded, deterministic LRU for retained computation caches.

The caller estimates owned bytes, excluding shared immutable inputs. A skipped
oversized entry changes reuse, never the mathematical result. Byte accounting
is a conservative estimate, not a process RSS guarantee.
"""
from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass
from typing import Generic, TypeVar

_K = TypeVar("_K")
_V = TypeVar("_V")


@dataclass(frozen=True)
class CachePolicy:
    max_bytes: int
    max_entries: int | None = None

    def __post_init__(self) -> None:
        if (type(self.max_bytes) is not int or self.max_bytes < 1 or
                (self.max_entries is not None and
                 (type(self.max_entries) is not int or self.max_entries < 0))):
            raise ValueError("Invalid cache retention budget")


class SharedCacheBudget:
    """Contraction-local aggregate of retained cache bytes across recursion.

    Individual caches may decline retention when the shared budget is full.
    Refusal to cache is never refusal to compute the exact value.
    """

    def __init__(self, max_bytes: int) -> None:
        if type(max_bytes) is not int or max_bytes < 1:
            raise ValueError("Shared cache budget must be a positive integer")
        self.max_bytes = max_bytes
        self._owners: dict[object, int] = {}
        self.live_bytes = 0
        self.peak_bytes = 0
        self.skipped_reservations = 0

    def try_set(self, owner: object, estimated_bytes: int) -> bool:
        if type(estimated_bytes) is not int or estimated_bytes < 0:
            raise ValueError("Shared cache reservation must be nonnegative")
        previous = self._owners.get(owner, 0)
        total = self.live_bytes - previous + estimated_bytes
        if total > self.max_bytes:
            self.skipped_reservations += 1
            return False
        if estimated_bytes:
            self._owners[owner] = estimated_bytes
        else:
            self._owners.pop(owner, None)
        self.live_bytes = total
        self.peak_bytes = max(self.peak_bytes, total)
        return True

    def release(self, owner: object) -> None:
        self.try_set(owner, 0)


class BudgetedLRU(Generic[_K, _V]):
    def __init__(
        self, policy: CachePolicy, *, shared: SharedCacheBudget | None = None,
    ) -> None:
        self.policy = policy
        self.shared = shared
        self._owner = object()
        self.skipped_shared_budget = 0
        self.entries: OrderedDict[_K, tuple[_V, int]] = OrderedDict()
        self.live_bytes = 0
        self.peak_bytes = 0
        self.peak_entries = 0
        self.hits = 0
        self.misses = 0
        self.evictions = 0
        self.skipped_oversize = 0

    def get(self, key: _K) -> _V | None:
        item = self.entries.get(key)
        if item is None:
            self.misses += 1
            return None
        self.entries.move_to_end(key)
        self.hits += 1
        return item[0]

    def put(self, key: _K, value: _V, estimated_bytes: int) -> bool:
        if estimated_bytes < 1:
            raise ValueError("Cached entry estimate must be positive")
        old = self.entries.pop(key, None)
        if old is not None:
            self.live_bytes -= old[1]
        if (self.policy.max_entries == 0 or
                estimated_bytes > self.policy.max_bytes):
            if self.shared is not None:
                self.shared.try_set(self._owner, self.live_bytes)
            self.skipped_oversize += 1
            return False
        while self.entries and (
            (self.policy.max_entries is not None and
             len(self.entries) >= self.policy.max_entries)
            or self.live_bytes + estimated_bytes > self.policy.max_bytes
        ):
            _, (_, removed_bytes) = self.entries.popitem(last=False)
            self.live_bytes -= removed_bytes
            self.evictions += 1
        if self.shared is not None and not self.shared.try_set(
            self._owner, self.live_bytes + estimated_bytes
        ):
            self.shared.try_set(self._owner, self.live_bytes)
            self.skipped_shared_budget += 1
            return False
        self.entries[key] = (value, estimated_bytes)
        self.live_bytes += estimated_bytes
        self.peak_bytes = max(self.peak_bytes, self.live_bytes)
        self.peak_entries = max(self.peak_entries, len(self.entries))
        return True

    def clear(self) -> None:
        self.entries.clear()
        self.live_bytes = 0
        if self.shared is not None:
            self.shared.release(self._owner)
