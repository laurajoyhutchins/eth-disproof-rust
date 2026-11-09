"""Resource policies for leaf execution and depth-scoped caches.

The reference result must not change when optional caching is disabled or
when a leaf falls back from compiled lookup tables to indexed evaluation.
"""
from __future__ import annotations

from dataclasses import replace
from itertools import product

import pytest

from non_exponential_sudoku import (
    CachePolicy, ContractionEngine, ContractorConfig, LeafConfig,
    ModeConfig, RecursionConfig,
)
from non_exponential_sudoku.contraction.compiled_children import CompiledChildPlan
from non_exponential_sudoku.contraction.workspaces import FrameWorkspace
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.network import compile_leaf_plan, simple_network
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.runtime.cache import BudgetedLRU
from benchmarks.recursive_cases import get_case

pytestmark = pytest.mark.checkpoint


def _network():
    choices = {bits: 1 for bits in product((0, 1), repeat=2)}
    return simple_network(
        2, [((0, 1), choices)], [((0,), {(0,): 1, (1,): 1}),
                                ((1,), {(0,): 1, (1,): 1})],
    )


def test_leaf_policy_is_validated_and_controls_python_elimination() -> None:
    net = _network()
    baseline = ContractionEngine(ContractorConfig(
        2, 9, schedule='micro', leaf=LeafConfig(strategy='eliminate',
                                               micro_threshold=2),
    )).contract(net)[0]
    assert baseline == 4

    configured = LeafConfig(strategy='eliminate', micro_threshold=2,
                            max_width=2, lookup_entries=0,
                            max_factor_bytes=128 * 1024)
    engine = ContractionEngine(ContractorConfig(2, 9, schedule='micro',
                                                leaf=configured))
    assert engine.contract(net)[0] == baseline

    tiny = replace(configured, max_factor_bytes=1)
    with pytest.raises(CapacityError, match='Leaf factor memory'):
        ContractionEngine(ContractorConfig(2, 9, schedule='micro',
                                           leaf=tiny)).contract(net)

    for changes in (dict(max_width=0), dict(lookup_entries=-1),
                    dict(max_factor_bytes=0)):
        with pytest.raises(ValueError, match='Leaf'):
            replace(configured, **changes)


def test_compiled_child_plan_honors_leaf_width_and_lookup_policy() -> None:
    net = _network()
    packing = pack(net, 2, 1)
    policy = LeafConfig(strategy='eliminate', limit=3, max_width=2,
                        lookup_entries=0)
    plan = CompiledChildPlan(net, packing, 0, 0, leaf=policy)
    assert plan.leaf_plan is not None
    assert plan.leaf_plan.max_width == 2
    assert all(step.lookup is None for step in plan.leaf_plan.steps)
    narrow = CompiledChildPlan(net, packing, 0, 0,
                               leaf=replace(policy, max_width=1))
    assert narrow.leaf_plan is None


def test_leaf_plan_lookup_entries_remain_an_explicit_budget() -> None:
    net = _network()
    scopes = tuple(v.ports for v in net.left + net.right)
    assert compile_leaf_plan(net.edges, scopes, lookup_budget=0) is not None
    assert all(step.lookup is None for step in
               compile_leaf_plan(net.edges, scopes, lookup_budget=0).steps)


def test_byte_bounded_cache_eviction_and_oversize_skip() -> None:
    cache: BudgetedLRU[str, int] = BudgetedLRU(
        CachePolicy(max_bytes=80, max_entries=None))
    assert cache.put('a', 1, 40)
    assert cache.put('b', 2, 40)
    assert cache.get('a') == 1
    assert cache.put('c', 3, 40)
    assert cache.get('b') is None
    assert cache.get('a') == 1
    assert cache.get('c') == 3
    assert not cache.put('oversize', 5, 81)
    assert cache.peak_bytes <= 80
    assert cache.live_bytes == 80
    assert cache.evictions == 1
    assert cache.skipped_oversize == 1
    cache.clear()
    assert cache.live_bytes == 0

    disabled: BudgetedLRU[str, int] = BudgetedLRU(
        CachePolicy(max_bytes=80, max_entries=0))
    assert not disabled.put('a', 1, 10)
    assert disabled.get('a') is None


def test_compiled_plan_cache_is_configurable_without_changing_plan() -> None:
    net = _network()
    packing = pack(net, 2, 1)
    limited = FrameWorkspace(
        cache_policy=CachePolicy(max_bytes=1),
        leaf=LeafConfig(max_width=2, lookup_entries=0),
    )
    first, hit = limited.get_plan(net, packing, 0, 0, None)
    assert not hit
    next_plan, hit = limited.get_plan(net, packing, 0, 0, None)
    assert not hit
    assert first.edges == next_plan.edges
    assert limited.plans.live_bytes == 0

    retained = FrameWorkspace(cache_policy=CachePolicy(max_bytes=1 << 20))
    cached, hit = retained.get_plan(net, packing, 0, 0, None)
    assert not hit
    repeated, hit = retained.get_plan(net, packing, 0, 0, None)
    assert hit and repeated is cached
    assert 0 < retained.plans.live_bytes <= (1 << 20)


def test_recursion_cache_policies_validate_at_construction() -> None:
    config = RecursionConfig(
        child_cache=CachePolicy(max_bytes=256, max_entries=0),
        compiled_plans=CachePolicy(max_bytes=512, max_entries=None),
    )
    assert config.child_cache.max_entries == 0
    assert config.compiled_plans.max_entries is None
    with pytest.raises(ValueError, match='cache'):
        CachePolicy(max_bytes=0)
    with pytest.raises(ValueError, match='cache'):
        CachePolicy(max_bytes=10, max_entries=-1)


def test_native_backend_honors_custom_leaf_policy() -> None:
    pytest.importorskip("native_recursive")
    net = _network()
    config = ContractorConfig(2, 9, schedule='micro',
                              leaf=LeafConfig(strategy='eliminate',
                                              micro_threshold=2,
                                              max_width=2, lookup_entries=0,
                                              max_factor_bytes=128 * 1024),
                              recursion=RecursionConfig(native_leaf=True))
    assert ContractionEngine(config).contract(net)[0] == 4
    tiny = replace(config, leaf=replace(config.leaf, max_factor_bytes=1))
    with pytest.raises(CapacityError, match='Leaf factor memory'):
        ContractionEngine(tiny).contract(net)


def test_byte_budgets_do_not_change_exact_enumerated_deformation() -> None:
    case = get_case('crossing-4wire', 'reference')
    # Force the explicit tuple path so child-result cache retention is used.
    reference = replace(case, config=replace(
        case.config, mode=ModeConfig(strategy='enumerate'))).run()[0]
    assert reference == case.expected
    for cache_bytes, entries in ((1, 0), (1, None), (1 << 20, 128)):
        config = replace(
            case.config,
            mode=ModeConfig(strategy='enumerate'),
            recursion=RecursionConfig(
                child_cache=CachePolicy(cache_bytes, entries),
                compiled_plans=CachePolicy(cache_bytes, entries),
            ),
        )
        got, stats = replace(case, config=config).run()
        assert got == reference
        assert stats.child_cache_peak_estimated_bytes <= cache_bytes
        assert stats.child_plan_cache_peak_estimated_bytes <= cache_bytes
