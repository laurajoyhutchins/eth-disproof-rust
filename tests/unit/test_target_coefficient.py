"""Exact coefficient extraction equivalence and state-growth contracts.

Synthetic disconnected families demonstrate avoidable exponential materialization.
Dense connected families deliberately preserve the permanent obstruction.
Neither is assumed realizable by an active paper-schedule Sudoku packet.
"""
from __future__ import annotations

from itertools import product
from math import factorial
from random import Random

import pytest

from non_exponential_sudoku.contraction.children import make_child
from non_exponential_sudoku.contraction.packets import EvaluationContext, PacketEntry
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.packing import pack
from reference.sudoku_network_oracle import port_graph_with_cross_mode
from reference.target_coefficient import (
    ExtractionStats, LinearRow, evaluate_packet_target_coefficient,
    expanded_coefficient_reference, target_coefficient_by_components,
)

pytestmark = pytest.mark.checkpoint


def _ring() -> Padic:
    return Padic(3, modulus_polynomial(3), 19)


def _independent(n: int, ring: Padic) -> tuple[LinearRow, ...]:
    return tuple(LinearRow(ring.one, ((j, ring.one),)) for j in range(n))


@pytest.mark.parametrize("n", [1, 2, 3, 5, 8, 11])
def test_independent_modes_need_no_exponential_table(n: int) -> None:
    ring = _ring()
    rows = _independent(n, ring)
    target = (1,) * n
    baseline, optimized = ExtractionStats(), ExtractionStats()
    expected = expanded_coefficient_reference(ring, rows, target, stats=baseline)
    result = target_coefficient_by_components(ring, rows, target, stats=optimized)
    assert expected == result == ring.one
    assert baseline.peak_states == (1 << n)
    assert optimized.components == n
    assert optimized.largest_component_modes == 1
    assert optimized.peak_states == 1
    assert optimized.retained_transitions == n
    assert optimized.states_visited == n
    assert optimized.pruned_transitions == n


@pytest.mark.parametrize("n", [2, 3, 5, 7])
def test_dense_connected_family_retains_permanent_obstruction(n: int) -> None:
    ring = _ring()
    rows = tuple(
        LinearRow(ring.zero, tuple((i, ring.one) for i in range(n)))
        for _ in range(n)
    )
    target = (1,) * n
    before, after = ExtractionStats(), ExtractionStats()
    got = target_coefficient_by_components(ring, rows, target, stats=after)
    plain = expanded_coefficient_reference(ring, rows, target, stats=before)
    assert got == plain == ring.scalar(factorial(n))
    assert after.components == 1
    assert after.largest_component_modes == n
    assert after.peak_states > 1
    assert after.peak_states <= before.peak_states


@pytest.mark.parametrize("blocks", [2, 3, 4])
def test_small_coupled_blocks_factor_without_cross_product(blocks: int) -> None:
    ring = _ring()
    rows = tuple(
        LinearRow(ring.zero, ((2*b, ring.one), (2*b+1, ring.one)))
        for b in range(blocks) for _ in range(2)
    )
    before, after = ExtractionStats(), ExtractionStats()
    target = (1,) * (2*blocks)
    assert expanded_coefficient_reference(ring, rows, target, stats=before) == (
        target_coefficient_by_components(ring, rows, target, stats=after)
    ) == ring.scalar(2**blocks)
    assert before.peak_states > after.peak_states
    assert after.components == blocks and after.largest_component_modes == 2
    assert after.peak_states <= 2



@pytest.mark.parametrize("n", [4, 6, 9])
def test_connected_sparse_incidence_still_reduces_intermediate_states(n: int) -> None:
    ring = _ring()
    # A connected cycle. Every row can choose its own mode or its successor.
    # The only full assignments are the two perfect matchings.
    rows = tuple(
        LinearRow(ring.zero, ((j, ring.one), ((j + 1) % n, ring.one)))
        for j in range(n)
    )
    goal = (1,) * n
    before, after = ExtractionStats(), ExtractionStats()
    old = expanded_coefficient_reference(ring, rows, goal, stats=before)
    new = target_coefficient_by_components(ring, rows, goal, stats=after)
    assert new == old == ring.scalar(2)
    assert after.components == 1
    assert after.largest_component_modes == n
    assert after.peak_states <= before.peak_states
    assert after.pruned_transitions > 0

def _enumerate_product(ring: Padic | JetRing,
                       rows: tuple[LinearRow, ...],
                       target: tuple[int, ...]) -> object:
    """Independent small exhaustive expansion with no dictionaries or DP."""
    result = ring.zero
    for selections in product(*(range(len(row.terms)+1) for row in rows)):
        powers = [0] * len(target)
        value = ring.one
        for row, choice in zip(rows, selections):
            if choice == 0:
                coefficient = row.constant
            else:
                index, coefficient = row.terms[choice-1]
                powers[index] += 1
            value = ring.mul(value, coefficient)
        if tuple(powers) == target:
            result = ring.add(result, value)
    return result


@pytest.mark.parametrize("jet", [False, True])
def test_bounded_random_polynomials_agree_with_independent_enumeration(jet: bool) -> None:
    seed = Random(20261109)
    base = _ring()
    ring = JetRing(base, 3) if jet else base
    for _ in range(40):
        n = seed.randrange(1, 5)
        m = seed.randrange(0, 6)
        target = tuple(seed.randrange(0, 3) for _ in range(n))
        rows = tuple(
            LinearRow(
                ring.scalar(seed.randrange(-3, 4)),
                tuple((seed.randrange(n), ring.scalar(seed.randrange(-3, 4)))
                      for _ in range(seed.randrange(0, 4))),
            ) for _ in range(m)
        )
        brute = _enumerate_product(ring, rows, target)
        old = expanded_coefficient_reference(ring, rows, target)
        new = target_coefficient_by_components(ring, rows, target)
        assert old == new == brute, (target, rows)


def test_missing_target_and_constants_are_exact() -> None:
    ring = _ring()
    rows = (
        LinearRow(ring.scalar(3), ((0, ring.one),)),
        LinearRow(ring.scalar(5), ((1, ring.one),)),
        LinearRow(ring.scalar(7), ()),
    )
    for target in ((0, 0), (1, 0), (0, 1), (1, 1), (2, 1), (1, 2)):
        assert target_coefficient_by_components(ring, rows, target) == (
            expanded_coefficient_reference(ring, rows, target)
        )
    assert target_coefficient_by_components(ring, rows, (0, 0)) == ring.scalar(105)
    assert target_coefficient_by_components(ring, rows, (1, 1)) == ring.scalar(7)
    assert target_coefficient_by_components(ring, rows, (1, 1, 1)) == ring.zero
    with pytest.raises(ValueError):
        target_coefficient_by_components(ring, rows, (-1, 0))
    with pytest.raises(ValueError):
        target_coefficient_by_components(ring, rows, (1,))
    with pytest.raises(ValueError):
        target_coefficient_by_components(ring, rows, (True, 0))


@pytest.mark.parametrize("jet", [False, True])
@pytest.mark.parametrize("precision", [9, 15])
def test_real_packet_terms_match_unmodified_eager_reference(jet: bool, precision: int) -> None:
    original = port_graph_with_cross_mode()
    packing = pack(original, 2, 1, (((0,),), ((1,),)))
    base = Padic(5, modulus_polynomial(5), precision)
    ring = JetRing(base, 2) if jet else base
    modes = mode_catalog(original, packing, 1, precision)
    assert modes
    nonempty = 0
    for beta in ((0,)*len(modes), (1,)*len(modes)):
        context = EvaluationContext(1, ring.one, ring, 1)
        for group in (0, 1):
            child = make_child(
                original, packing, modes, beta, 1, ring.one, ring,
                group, 0, context,
            )
            for vertex in child.right:
                entry = vertex.oracle
                assert isinstance(entry, PacketEntry)
                nonempty += bool(entry.terms.desired)
                for bits in product((0, 1), repeat=len(vertex.ports)):
                    stats = ExtractionStats()
                    actual = evaluate_packet_target_coefficient(entry, bits, stats=stats)
                    expected = entry._evaluate_python(bits)
                    assert actual == expected, (jet, precision, beta, group, bits)
    assert nonempty > 0


def test_experimental_path_rejects_native_or_lazy_packet() -> None:
    source = port_graph_with_cross_mode()
    packing = pack(source, 2, 1, (((0,),), ((1,),)))
    ring = _ring()
    modes = mode_catalog(source, packing, 1, ring.p)
    child = make_child(
        source, packing, modes, (1,)*len(modes),
        1, ring.one, ring, 0, 0,
        EvaluationContext(1, ring.one, ring, 1),
    )
    entry = next(v.oracle for v in child.right if isinstance(v.oracle, PacketEntry))
    bits = (0,) * len(next(v.ports for v in child.right if v.oracle is entry))
    entry.native = object()  # type: ignore[assignment]
    with pytest.raises(TypeError, match="eager Python"):
        evaluate_packet_target_coefficient(entry, bits)
    entry.native = None
    entry.work_ring = object()  # type: ignore[assignment]
    with pytest.raises(TypeError, match="eager Python"):
        evaluate_packet_target_coefficient(entry, bits)
