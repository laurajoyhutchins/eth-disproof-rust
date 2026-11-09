"""The global cache budget coordinates *retained* memory, not arithmetic RSS."""
from __future__ import annotations

from dataclasses import replace

import pytest

from benchmarks.recursive_cases import get_case
from non_exponential_sudoku import CachePolicy, ContractionEngine, RecursionConfig
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.runtime.cache import BudgetedLRU, SharedCacheBudget
from non_exponential_sudoku.contraction.workspaces import FrameWorkspace

pytestmark = pytest.mark.checkpoint


def test_shared_pool_rejects_cross_cache_retention_and_recovers_on_release() -> None:
    budget = SharedCacheBudget(100)
    first: BudgetedLRU[str, int] = BudgetedLRU(CachePolicy(100), shared=budget)
    second: BudgetedLRU[str, int] = BudgetedLRU(CachePolicy(100), shared=budget)
    assert first.put("one", 1, 70)
    assert not second.put("two", 2, 50)
    assert budget.live_bytes == 70
    assert budget.peak_bytes == 70
    assert second.skipped_shared_budget == 1
    first.clear()
    assert budget.live_bytes == 0
    assert second.put("two", 2, 50)
    assert budget.live_bytes == 50
    second.clear()
    assert budget.live_bytes == 0


def test_shared_pool_eviction_and_replacement_do_not_leak_reservations() -> None:
    budget = SharedCacheBudget(100)
    cache: BudgetedLRU[str, int] = BudgetedLRU(
        CachePolicy(max_bytes=80, max_entries=2), shared=budget)
    assert cache.put("one", 1, 40)
    assert cache.put("two", 2, 40)
    assert cache.put("three", 3, 40)
    assert budget.live_bytes == 80
    assert cache.evictions == 1
    assert cache.put("three", 4, 60)
    assert budget.live_bytes == 60
    assert cache.live_bytes == 60
    cache.clear()
    assert budget.live_bytes == 0


def test_recursion_shared_budget_validation() -> None:
    assert RecursionConfig().shared_cache_bytes is None
    assert RecursionConfig(shared_cache_bytes=1024).shared_cache_bytes == 1024
    for value in (0, -1, True):
        with pytest.raises(ValueError, match="shared cache"):
            RecursionConfig(shared_cache_bytes=value)


def test_nested_exactness_with_tight_shared_cache_budget() -> None:
    case = get_case("nested-2wire", "plans")
    reference = ContractionEngine(case.config)
    expected = reference.contract(case.network)
    configured = replace(
        case.config,
        recursion=replace(case.config.recursion, shared_cache_bytes=1024,
                          compiled_plans=CachePolicy(8192, 64),
                          child_cache=CachePolicy(8192, 128)),
    )
    engine = ContractionEngine(configured)
    assert engine.contract(case.network) == expected
    assert engine.stats.shared_cache_peak_estimated_bytes <= 1024
    assert engine.shared_cache is not None
    assert engine.shared_cache.live_bytes == 0
    assert engine._frames == {}
    assert engine.contract(case.network) == expected
    assert engine.shared_cache.live_bytes == 0


def test_shared_budget_clears_on_recursive_refusal() -> None:
    case = get_case("nested-2wire", "plans")
    configured = replace(
        case.config,
        recursion=replace(case.config.recursion, shared_cache_bytes=4096),
    )
    engine = ContractionEngine(configured)
    with pytest.MonkeyPatch.context() as patch:
        def stop(*_args: object, **_kwargs: object) -> None:
            raise CapacityError("Deliberate child refusal")
        patch.setattr(FrameWorkspace, "get_plan", stop)
        with pytest.raises(CapacityError, match="Deliberate child refusal"):
            engine.contract(case.network)
    assert engine.shared_cache is not None
    assert engine.shared_cache.live_bytes == 0
    assert engine._frames == {}
    assert engine.contract(case.network)[0] == case.expected
