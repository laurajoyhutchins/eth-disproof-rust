"""Conditional center-work tests: independent mode assignments and source DP.

These don't turn a table-operation bound into a bit-cost theorem, and don't
claim that finite artificial mode lists are full paper-admitted packings.
"""
from __future__ import annotations

from itertools import product

import pytest
from math import isqrt

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.modes import Mode
from non_exponential_sudoku.elimination.engine import ModeEliminator
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.runtime.config import ModeLimits
from non_exponential_sudoku.runtime.statistics import Counters
from non_exponential_sudoku.runtime.cost_ledger import CostLedger
from reference.center_evaluation_work import (
    paper_center_work_envelope, ring_convolution_upper,
    table_child_call_bound,
)
from reference.precision_envelope import paper_frame_envelopes
from non_exponential_sudoku.runtime.config import ContractorConfig

pytestmark = pytest.mark.checkpoint


def brute_weighted_assignments(modes: list[Mode], precision: int) -> int:
    return sum(
        sum(b * m.weight for b, m in zip(beta, modes)) < precision
        for beta in product(*(range(len(m.rows) + 1) for m in modes))
    )


@pytest.mark.parametrize('join', ['sparse', 'enumerate'])
@pytest.mark.parametrize('p', [3, 5, 7])
@pytest.mark.parametrize('weights', [(1,), (1, 2), (1, 1, 2)])
def test_factor_child_evaluations_lie_in_global_weighted_domain(
    p: int, weights: tuple[int, ...], join: str,
) -> None:
    modes = [Mode(j, 0, w-1, 0, 1, w, (), (0,)) for j, w in enumerate(weights)]
    R = Padic(3, modulus_polynomial(3), p)
    stats = Counters()
    actual_keys: list[tuple[int, ...]] = []

    def oracle(_g: int, _scope: tuple[int, ...], assignment: tuple[int, ...]):
        actual_keys.append(assignment)
        return R.one

    limits = ModeLimits(max_components=1000, max_factor_states=10_000,
                        max_live_terms=100_000, max_operations=2_000_000,
                        max_child_contractions=1_000_000,
                        max_estimated_bytes=128 * 1024 * 1024)
    ledger = CostLedger()
    with ledger.frame(depth=0, wires=0, precision=p, ring_depth=0,
                      schedule='micro'):
        observed = ModeEliminator(
            modes, {0, 1}, R, oracle, stats, CapacityError,
            join_strategy=join, native_sparse=False, limits=limits,
        ).run()
    domain_count = brute_weighted_assignments(modes, p)
    assert observed == R.scalar(domain_count)
    assert len(actual_keys) == 2 * domain_count
    assert stats.mode_dp_local_child_evaluations == len(actual_keys)
    assert stats.mode_dp_local_child_evaluations <= table_child_call_bound(
        factors=2, admissible_assignments=domain_count,
    )
    assert stats.mode_dp_peak_factor_states <= table_child_call_bound(
        factors=2, admissible_assignments=domain_count,
    )
    assert sum(ledger.total_ring_calls.values()) <= ring_convolution_upper(
        eliminations=len(modes), factors=2, factor_rows=domain_count,
        precision=p,
    )
    # Budget work units also include non-ring table and ordering work, so
    # do not use them as a bit-operation oracle.
    assert stats.mode_dp_operations <= ring_convolution_upper(
        eliminations=len(modes), factors=2, factor_rows=domain_count,
        precision=p,
    )


@pytest.mark.parametrize('i', [0, 1, 2])
def test_center_precision_taper_and_child_fanout(i: int) -> None:
    M, V, P, L, u, p = 320, 400, 10, 64, 3, 17
    assert P * L <= 3 * M
    w = paper_center_work_envelope(edges=M, vertices=V, packet_count=P,
                                   slots=L, groups=64, active_coordinates=u,
                                   center_valuation=i, base_precision=p)
    h = (3 * M + u - 1) // u
    assert w.center_precision == p + 8 * h * (L >> i) + 8 * M * 7
    assert w.colors_per_weight == P * (1 << (i + 1))
    assert w.sample_count == M * 127 + 1
    assert w.mode_count_ceiling == w.colors_per_weight * (w.center_precision-1)
    assert (1 << w.log2_factor_child_calls) >= w.factor_count_ceiling
    assert w.log2_center_child_calls >= w.log2_factor_child_calls
    assert w.log2_center_ring_calls >= w.log2_factor_join_pairs


def test_no_precision_taper_means_a_weaker_product_estimate() -> None:
    M,V,P,L,u,p=320,400,10,64,3,17
    centers=[paper_center_work_envelope(edges=M,vertices=V,packet_count=P,
              slots=L,groups=64,active_coordinates=u,center_valuation=i,
              base_precision=p) for i in range(u)]
    maxK=max(x.colors_per_weight for x in centers)
    maxP=max(x.center_precision for x in centers)
    actual=max(x.colors_per_weight * x.center_precision for x in centers)
    assert actual < maxK * maxP


def test_active_paper_symbolic_schedule_no_gigantic_modes() -> None:
    # A genuinely paper-active symbolic frame is inaccessible to material
    # tests. Show the algorithm's formulas compose without allocating mode
    # catalogs, support tables, or giant coefficient rings.
    lam=131072
    s=(1 << (lam-1))+1
    cfg=ContractorConfig(s=s,precision=33,schedule='paper')
    frames=paper_frame_envelopes(cfg,edges=s,vertices=s)
    assert frames[0].terminal is False
    f=frames[0]
    P=(3 * f.edges)//f.slots
    for i in range(1):
        w=paper_center_work_envelope(edges=f.edges,vertices=f.vertices,
             packet_count=P,slots=f.slots,groups=64,active_coordinates=1,
             center_valuation=i,base_precision=f.precision)
        # The first active schedule has u=1. Its intentionally loose
        # finite bound may exceed s; an asymptotic o(s) theorem does NOT
        # imply a finite bound below s at every size.
        assert w.support_exponent == 4 * (isqrt(w.colors_per_weight * w.center_precision - 1) + 1)
        assert w.log2_center_child_calls >= w.support_exponent
        assert w.log2_center_ring_calls >= 2 * w.support_exponent
        with pytest.raises(ValueError, match='not materialized'):
            w.child_call_capacity_small()


@pytest.mark.parametrize('bad', [
    {'slots':3}, {'active_coordinates':4,'slots':64},
    {'packet_count':10000}, {'center_valuation':3},
    {'base_precision':0}, {'groups':0}
])
def test_center_bound_rejects_unadmitted_premises(bad: dict[str,int]) -> None:
    args=dict(edges=320,vertices=400,packet_count=10,slots=64,
              groups=64,active_coordinates=3,center_valuation=0,base_precision=17)
    with pytest.raises(ValueError):
        paper_center_work_envelope(**(args | bad))


@pytest.mark.parametrize('strategy', ['whole', 'components'])
def test_real_factor_plan_count_fits_incidence_component_envelope(
    strategy: str,
) -> None:
    """Inspect real child-graph components, not just artificial factor scopes.

    The finite fixture is outside the active paper size regime; the bound
    comes from each component containing a retained vertex or packet node.
    """
    from non_exponential_sudoku.contraction.planning import build_factorization_plan
    from non_exponential_sudoku.core.modes import mode_catalog
    from non_exponential_sudoku.core.packing import pack
    from reference.sudoku_network_oracle import port_graph_with_cross_mode

    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    modes = mode_catalog(net, packing, 1, 9)
    occupied = {labels[0] for labels in packing.groups_left + packing.groups_right}
    affected = {g: tuple(j for j, m in enumerate(modes)
                         if m.source == g or m.target == g) for g in occupied}
    plan = build_factorization_plan(net, packing, modes, 0, occupied, affected,
                                    strategy=strategy)
    assert len(plan.factors) <= (packing.r *
                                 (len(net.left) + len(net.right)
                                  + len(packing.packets) + 1))
