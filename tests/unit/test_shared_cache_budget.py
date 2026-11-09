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


def test_prepared_packet_and_packet_entry_memo_share_retention() -> None:
    from non_exponential_sudoku.contraction.compiled_children import CompiledChildPlan
    from non_exponential_sudoku.contraction.packets import (
        BoundedPacketMemo, EvaluationContext, PreparedPacketCache,
        _prepared_owned_bytes,
    )
    from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
    from non_exponential_sudoku.core.modes import mode_catalog
    from non_exponential_sudoku.core.packing import pack
    from non_exponential_sudoku.sudoku.encoding import port_graph_with_cross_mode

    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    ring = Padic(5, modulus_polynomial(5), 13)
    modes = mode_catalog(net, packing, 1, ring.p)
    plan = CompiledChildPlan(net, packing, 0, 0)
    context = EvaluationContext(1, ring.one, ring, 1)
    oracle = plan.instantiate(modes, (0,) * len(modes),
                              1, ring.one, ring, context).right[0].oracle
    key = ("prepared",)
    estimate = _prepared_owned_bytes(key, oracle)
    shared = SharedCacheBudget(estimate)
    prepared = PreparedPacketCache(8, max_bytes=estimate, shared=shared)
    memo = BoundedPacketMemo(ring, entries=8, max_bytes=estimate,
                             shared=shared)
    prepared.put(key, oracle)
    assert shared.live_bytes == estimate
    memo.put(("memo",), ring.one)
    assert memo.skipped_shared_budget == 1
    assert memo.live_bytes == 0
    prepared.clear()
    assert shared.live_bytes == 0
    assert memo.entry_bytes <= estimate
    memo.put(("memo",), ring.one)
    assert memo.live_bytes == memo.entry_bytes
    assert shared.live_bytes == memo.entry_bytes
    memo.clear()
    assert shared.live_bytes == 0


def test_shared_pool_rejects_invalid_requests_without_changing_state() -> None:
    budget = SharedCacheBudget(20)
    owner = object()
    assert budget.try_set(owner, 11)
    assert not budget.try_set(owner, 21)
    assert budget.live_bytes == 11
    assert budget.skipped_reservations == 1
    with pytest.raises(ValueError, match="reservation"):
        budget.try_set(owner, -1)
    budget.release(owner)
    assert budget.live_bytes == 0
