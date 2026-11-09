"""Reuse only a prepared internal packet, never an arbitrary child result."""
from __future__ import annotations

from dataclasses import replace
from itertools import product

import pytest

from benchmarks.recursive_cases import get_case
from non_exponential_sudoku import ContractionEngine, RecursionConfig
from non_exponential_sudoku.contraction.compiled_children import CompiledChildPlan
from non_exponential_sudoku.contraction.packets import EvaluationContext
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.modes import Mode, mode_catalog
from non_exponential_sudoku.core.packing import pack
from reference.sudoku_network_oracle import port_graph_with_cross_mode

pytestmark = pytest.mark.checkpoint


def test_preparation_reuses_only_equal_active_packet_modes_at_one_center() -> None:
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    ring = Padic(5, modulus_polynomial(5), 13)
    modes = mode_catalog(net, packing, 1, ring.p)
    zeros = (0,) * len(modes)
    plan = CompiledChildPlan(net, packing, 0, 0)
    ctx = EvaluationContext(1, ring.one, ring, 1, prepared_packet_entries=1)

    first = plan.instantiate(modes, zeros, 1, ring.one, ring, ctx)
    repeated = plan.instantiate(modes, zeros, 1, ring.one, ring, ctx)
    assert first is not repeated  # We never reuse a whole child contraction.
    assert first.right[0].oracle is repeated.right[0].oracle
    assert ctx.prepared_packets is not None
    assert ctx.prepared_packets.hits == 1

    # A mode on some unrelated packet cannot change this packet's coefficients.
    unrelated = Mode(-1, 0, 0, 0, 1, 1, (), ())
    also_same = plan.instantiate(modes + [unrelated], zeros + (1,),
                                 1, ring.one, ring, ctx)
    assert first.right[0].oracle is also_same.right[0].oracle

    packet_id = first.right[0].oracle.packet_id
    assert any(mode.packet == packet_id for mode in modes)
    active = tuple(1 if mode.packet == packet_id else 0 for mode in modes)
    changed = plan.instantiate(modes, active, 1, ring.one, ring, ctx)
    assert changed.right[0].oracle is not first.right[0].oracle
    assert ctx.prepared_packets.evictions >= 1
    assert ctx.prepared_packets.peak_entries == 1

    recreated = plan.instantiate(modes, zeros, 1, ring.one, ring, ctx)
    assert recreated.right[0].oracle is not first.right[0].oracle
    assert recreated.right[0].oracle((0,) * len(recreated.right[0].ports), ring) == (
        first.right[0].oracle((0,) * len(first.right[0].ports), ring)
    )

    other_center = EvaluationContext(1, ring.one, ring, 1, prepared_packet_entries=1)
    separate = plan.instantiate(modes, zeros, 1, ring.one, ring, other_center)
    assert separate.right[0].oracle is not recreated.right[0].oracle

    # Compare cached and independently prepared coefficients for all binary
    # assignments, rather than assuming the cache's identity test is enough.
    reference = plan.instantiate(modes, active, 1, ring.one, ring,
                                 EvaluationContext(1, ring.one, ring, 1))
    for candidate, original in zip(changed.right, reference.right):
        for bits in product((0, 1), repeat=len(candidate.ports)):
            assert candidate.oracle(bits, ring) == original.oracle(bits, ring)


def test_prepared_packet_cache_disabled_for_lazy_coefficient_dags() -> None:
    base = Padic(5, modulus_polynomial(5), 13)
    ring = JetRing(base, 2)
    ctx = EvaluationContext(1, ring.one, ring, 1,
                            packet_coeff_cache_limit=0, prepared_packet_entries=32)
    assert ctx.prepared_packets is None


@pytest.mark.parametrize('entries', [-1])
def test_invalid_preparation_budgets_refused(entries: int) -> None:
    with pytest.raises(ValueError, match='prepared packet budget'):
        RecursionConfig(prepared_packet_entries=entries)


def test_preparation_requires_compiled_topology() -> None:
    with pytest.raises(ValueError, match='requires compiled child plans'):
        RecursionConfig(child_plans=False, prepared_packet_entries=8)


def test_preparation_reuse_preserves_recursive_work_and_exact_result() -> None:
    case = get_case('nested-2wire', 'plans')
    baseline = ContractionEngine(case.config)
    expected = baseline.contract(case.network)
    config = replace(case.config, recursion=replace(
        case.config.recursion, prepared_packet_entries=16,
    ))
    optimized = ContractionEngine(config)
    assert optimized.contract(case.network) == expected
    assert optimized.stats.child_networks == baseline.stats.child_networks
    assert optimized.stats.recursive_calls == baseline.stats.recursive_calls
    assert optimized.stats.prepared_packet_hits > 0
    assert optimized.stats.prepared_packet_misses > 0
    assert optimized.stats.prepared_packet_peak_entries <= 16


def test_prepared_cache_rejects_oversize_entry_and_bounds_estimated_bytes() -> None:
    from non_exponential_sudoku.contraction.packets import PreparedPacketCache

    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    ring = Padic(5, modulus_polynomial(5), 13)
    modes = mode_catalog(net, packing, 1, ring.p)
    zeros = (0,) * len(modes)
    plan = CompiledChildPlan(net, packing, 0, 0)

    context = EvaluationContext(1, ring.one, ring, 1,
                                prepared_packet_entries=4,
                                prepared_packet_bytes=1)
    plan.instantiate(modes, zeros, 1, ring.one, ring, context)
    cache = context.prepared_packets
    assert cache is not None
    assert cache.skipped_oversize > 0
    assert cache.live_bytes == 0
    assert cache.peak_bytes == 0

    # The budget includes keys and prepared coefficient structures.
    context = EvaluationContext(1, ring.one, ring, 1,
                                prepared_packet_entries=2,
                                prepared_packet_bytes=10_000)
    plan.instantiate(modes, zeros, 1, ring.one, ring, context)
    plan.instantiate(modes, zeros, 1, ring.one, ring, context)
    cache = context.prepared_packets
    assert cache is not None
    assert cache.hits > 0
    assert 0 < cache.live_bytes <= cache.max_bytes
    assert 0 < cache.peak_bytes <= cache.max_bytes
    cache.clear()
    assert cache.live_bytes == 0
    assert not cache.values
    assert not cache.sizes


@pytest.mark.parametrize('budget', [0, -1])
def test_invalid_prepared_packet_byte_budget(budget: int) -> None:
    with pytest.raises(ValueError, match='prepared packet budget'):
        RecursionConfig(prepared_packet_bytes=budget)


def test_prepared_packet_peak_estimated_bytes_recorded() -> None:
    case = get_case('nested-2wire', 'plans')
    config = replace(case.config, recursion=replace(
        case.config.recursion, prepared_packet_entries=16,
        prepared_packet_bytes=4096,
    ))
    engine = ContractionEngine(config)
    assert engine.contract(case.network)[0] == case.expected
    assert 0 < engine.stats.prepared_packet_peak_estimated_bytes <= 4096
    assert engine.stats.prepared_packet_hits > 0


def test_byte_limit_eviction_even_below_entry_limit() -> None:
    from non_exponential_sudoku.contraction.packets import (
        PreparedPacketCache, _prepared_owned_bytes,
    )
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    ring = Padic(5, modulus_polynomial(5), 13)
    modes = mode_catalog(net, packing, 1, ring.p)
    plan = CompiledChildPlan(net, packing, 0, 0)
    context = EvaluationContext(1, ring.one, ring, 1)
    zeros = (0,) * len(modes)
    first = plan.instantiate(modes, zeros, 1, ring.one, ring, context).right[0].oracle
    packet_id = first.packet_id
    active = tuple(1 if mode.packet == packet_id else 0 for mode in modes)
    second = plan.instantiate(modes, active, 1, ring.one, ring, context).right[0].oracle
    key1 = ('one',)
    key2 = ('two',)
    size1 = _prepared_owned_bytes(key1, first)
    size2 = _prepared_owned_bytes(key2, second)
    cap = max(size1, size2)
    assert cap < size1 + size2
    cache = PreparedPacketCache(limit=4, max_bytes=cap)
    cache.put(key1, first)
    cache.put(key2, second)
    assert cache.evictions == 1
    assert cache.peak_entries == 1
    assert len(cache.values) == 1
    assert cache.live_bytes <= cap
    assert cache.peak_bytes <= cap
