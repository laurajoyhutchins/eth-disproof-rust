"""Independent TDD checks for conditional global mode-factor support.

These verify the weighted-domain theorem and the *literal* paper schedule.
They do not treat capacity refusal as completion or certify bit-operation work.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import prod
from random import Random

import pytest

from non_exponential_sudoku.core.modes import mode_catalog, weighted_tuples
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.runtime.config import ContractorConfig
from reference.sudoku_network_oracle import port_graph_with_cross_mode
from reference.global_mode_support import (
    center_color_precision_product, colored_partition_log2_ceiling,
    exact_weighted_assignment_count, paper_global_mode_support_envelopes,
    uniform_support_ratio_square_bound, uniform_label_pair_paper_witness,
)
from reference.precision_envelope import paper_frame_envelopes


@pytest.mark.checkpoint
def test_colored_partitions_bound_small_independent_assignments() -> None:
    for precision in range(1, 10):
        for colors in range(4):
            weights = tuple(w for w in range(1, precision) for _ in range(colors))
            exact = exact_weighted_assignment_count(
                weights, tuple(precision for _ in weights), precision,
            )
            exponent = colored_partition_log2_ceiling(colors, precision)
            assert exact <= 1 << exponent
            if colors == 0 or precision == 1:
                assert exact == 1


@pytest.mark.checkpoint
def test_weighted_assignment_reference_agrees_with_separate_exhaustion() -> None:
    rng = Random(11665)
    for _ in range(120):
        n = rng.randrange(8)
        p = rng.randrange(1, 10)
        weights = tuple(rng.randrange(1, 6) for _ in range(n))
        caps = tuple(rng.randrange(3) for _ in range(n))
        direct = sum(
            sum(w * b for w, b in zip(weights, assignment)) < p
            for assignment in product(*(range(cap + 1) for cap in caps))
        )
        assert exact_weighted_assignment_count(weights, caps, p) == direct


@pytest.mark.checkpoint
def test_actual_mode_catalog_obeys_weight_colors_and_precision_budget() -> None:
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    for t in (-1, 1):
        for p in (3, 5, 9):
            modes = mode_catalog(net, packing, t, p)
            colors = len(packing.packets) * 2  # i = v2(t) = 0
            for weight in range(1, p):
                assert sum(m.weight == weight for m in modes) <= colors
            exact = exact_weighted_assignment_count(
                tuple(m.weight for m in modes),
                tuple(min(len(m.rows), (p - 1) // m.weight) for m in modes), p,
            )
            assert exact <= 1 << colored_partition_log2_ceiling(colors, p)


@pytest.mark.checkpoint
def test_actual_factor_scope_admissible_count_fits_global_ceiling() -> None:
    from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
    from non_exponential_sudoku.runtime.budget import CapacityError
    from non_exponential_sudoku.runtime.statistics import Counters
    from non_exponential_sudoku.elimination.engine import ModeEliminator

    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    p = 5
    modes = mode_catalog(net, packing, 1, p)
    ring = Padic(3, modulus_polynomial(3), p)
    seen: list[tuple[tuple[int, ...], tuple[int, ...]]] = []

    def child(_group: object, scope: tuple[int, ...], assignment: tuple[int, ...]) -> tuple[int, ...]:
        seen.append((scope, assignment))
        assert sum(modes[j].weight * b for j, b in zip(scope, assignment)) < p
        return ring.one

    eliminator = ModeEliminator(
        modes, {0, 1}, ring, child, Counters(), CapacityError,
        native_sparse=False,
    )
    # The full all-one factor graph is small enough here to be exact.
    assert eliminator.run() == ring.scalar(
        exact_weighted_assignment_count(
            tuple(m.weight for m in modes),
            tuple(min(len(m.rows), (p - 1) // m.weight) for m in modes), p,
        )
    )
    full_scope = tuple(range(len(modes)))
    full_count = exact_weighted_assignment_count(
        tuple(m.weight for m in modes),
        tuple(min(len(m.rows), (p - 1) // m.weight) for m in modes), p,
    )
    assert seen
    assert all(exact_weighted_assignment_count(
        tuple(modes[j].weight for j in scope),
        tuple(min(len(modes[j].rows), (p - 1) // modes[j].weight) for j in scope), p,
    ) <= full_count for scope, _ in seen)
    for factor in eliminator.factors:
        assert not factor.scope
        assert len(factor.table) <= 1
    assert full_count <= (1 << colored_partition_log2_ceiling(len(packing.packets) * 2, p))



@pytest.mark.checkpoint
def test_observed_sparse_factor_joins_cannot_escape_weighted_support() -> None:
    from benchmarks.growth_probe import GrowthCollector
    from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
    from non_exponential_sudoku.runtime.budget import CapacityError
    from non_exponential_sudoku.runtime.statistics import Counters
    from non_exponential_sudoku.elimination.engine import ModeEliminator
    from tests.support.mode_factors import synthetic_modes

    p = 6
    ring = Padic(3, modulus_polynomial(3), p)
    pairs = [(0, 1), (1, 2), (2, 3), (0, 3)]
    modes = synthetic_modes(pairs, p)
    caps = tuple(min(len(m.rows), (p - 1) // m.weight) for m in modes)
    global_count = exact_weighted_assignment_count(
        tuple(m.weight for m in modes), caps, p,
    )
    stats = Counters()
    trace = GrowthCollector()
    stats.growth_probe = trace
    eliminator = ModeEliminator(
        modes, {0, 1, 2, 3}, ring,
        lambda group, scope, beta: ring.one,
        stats, CapacityError, join_strategy='sparse', native_sparse=False,
    )
    assert eliminator.run() == ring.scalar(global_count)
    assert trace.records and trace.records[0]['status'] == 'completed'
    assert trace.records[0]['join_observations'] > 0
    assert trace.max_factor_states <= global_count
    assert trace.records[0]['max_admissible_states'] <= global_count
    assert trace.records[0]['planned_child_evaluations_upper_bound'] <= (
        len(eliminator.groups) * global_count
    )


@pytest.mark.integration
def test_tapered_center_product_bound_for_all_paper_valuations() -> None:
    for lam in (131072, 262144, 524288, 1048576):
        s = (1 << (lam - 1)) + 1
        cfg = ContractorConfig(s=s, precision=33, schedule='paper')
        frames = paper_frame_envelopes(cfg, s, s)
        for frame, bound in zip((f for f in frames if not f.terminal),
                                paper_global_mode_support_envelopes(cfg, edges=s, vertices=s)):
            L = frame.slots
            a = L.bit_length() - 1
            u = bound.active_coordinates
            P = bound.packet_count_ceiling
            h = (3 * frame.edges + u - 1) // u
            assert P * L <= 3 * frame.edges
            for i in range(u):
                K = P * (1 << (i + 1))
                pt = (frame.precision + 8 * h * (L >> i)
                      + 8 * frame.edges * (a + 1))
                assert K * pt <= bound.color_precision_product_ceiling
                assert colored_partition_log2_ceiling(K, pt) <= bound.log2_support_ceiling


@pytest.mark.integration
def test_uniform_symbolic_bound_dominates_every_paper_frame() -> None:
    for lam in (131072, 262144, 524288, 1048576):
        s = (1 << (lam - 1)) + 1
        cfg = ContractorConfig(s=s, precision=33, schedule='paper')
        ratio = uniform_support_ratio_square_bound(lam)
        for bound in paper_global_mode_support_envelopes(cfg, edges=s, vertices=s):
            assert Fraction(bound.color_precision_product_ceiling, s * s) <= ratio


@pytest.mark.checkpoint
def test_uniform_ratio_decreases_without_constructing_astronomical_sudoku() -> None:
    # These finite integer comparisons are regression witnesses, NOT a proof
    # of the limit. The uniform limit is proved by splitting depths into
    # d <= (log2 lambda)/2 and d greater than that threshold.
    ratios = [uniform_support_ratio_square_bound(lam) for lam in (
        131072, 262144, 524288, 1048576, 2**24, 2**28, 2**32, 2**40,
    )]
    assert all(a > b > 0 for a, b in zip(ratios, ratios[1:]))
    assert ratios[-1] < Fraction(1, 10000)


@pytest.mark.checkpoint
def test_global_state_bound_never_promotes_capacity_refusal_to_completion() -> None:
    from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
    from non_exponential_sudoku.runtime.budget import CapacityError
    from tests.support.mode_factors import dp_sum, synthetic_modes

    ring = Padic(5, modulus_polynomial(5), 9)
    modes = synthetic_modes([(0, 1)] * 8, ring.p)
    # Even though a finite, rigorous support bound exists, the current
    # production budget is allowed to refuse instead of completing.
    assert colored_partition_log2_ceiling(8, ring.p) > 0
    with pytest.raises(CapacityError):
        dp_sum(modes, ring, lambda *a: ring.one, max_factor_states=20)


@pytest.mark.checkpoint
def test_invalid_admission_and_count_inputs_refuse() -> None:
    with pytest.raises(ValueError):
        colored_partition_log2_ceiling(-1, 3)
    with pytest.raises(ValueError):
        colored_partition_log2_ceiling(2, 0)
    with pytest.raises(ValueError):
        exact_weighted_assignment_count((1,), (), 5)
    with pytest.raises(ValueError):
        exact_weighted_assignment_count((-1,), (1,), 5)
    with pytest.raises(ValueError):
        center_color_precision_product(edges=10, packet_count=100, slots=4,
                                       active_coordinates=1, precision=5)
    with pytest.raises(ValueError):
        center_color_precision_product(edges=10, packet_count=1, slots=4,
                                       active_coordinates=2, precision=5)
    with pytest.raises(ValueError):
        uniform_support_ratio_square_bound(0)


@pytest.mark.checkpoint
def test_symbolic_uniform_packing_meets_actual_paper_numeric_hypotheses() -> None:
    # A mathematical family of degree-one edges with each ordered pair of
    # supplied endpoint labels repeated equally. It is not materialized or
    # assumed to be the default greedy balanced_labels() output.
    for lam in (131072, 262144, 524288):
        w = uniform_label_pair_paper_witness(lam)
        assert w.admitted_numeric_hypotheses
        assert w.max_actual_degree == 1
        assert w.edges == w.full_pair_label_classes * w.edges_per_class
        assert w.edges == w.packet_count * w.packet_slots
        assert w.group_side_port_load * 64 == w.edges
        assert w.vertex_count == 2 * w.edges
    with pytest.raises(ValueError):
        uniform_label_pair_paper_witness(131071)
