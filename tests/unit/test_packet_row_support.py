"""TDD for exact packet-row degree restrictions and their asymptotic limit."""
from __future__ import annotations

from itertools import product
import random
from typing import Literal, cast
from math import isqrt

import pytest

from non_exponential_sudoku.contraction.children import make_child
from non_exponential_sudoku.contraction.packets import EvaluationContext, PacketEntry
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.modes import Mode, mode_catalog, weighted_tuples
from non_exponential_sudoku.core.network import simple_network
from non_exponential_sudoku.core.jets import NestedRing
from non_exponential_sudoku.contraction.engine import ContractionEngine
from non_exponential_sudoku.sudoku.encoding import independently_evaluate_F
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.elimination.engine import ModeEliminator
from non_exponential_sudoku.elimination.factors import FactorBuilder
from non_exponential_sudoku.runtime.budget import CapacityError, ModeBudget
from non_exponential_sudoku.runtime.config import ModeLimits, ModeConfig, ContractorConfig
from non_exponential_sudoku.runtime.statistics import Counters
from reference.packet_row_support import (
    brute_row_capped_assignments, hall_packet_rows_possible,
    passes_packet_row_caps, target_packet_row_caps,
    uniform_paper_row_capacity_witness,
)

pytestmark = pytest.mark.checkpoint


def _modes() -> list[Mode]:
    return [Mode(0, 0, 0, 1, 0, 1, ((0, 0),), (0,)),
            Mode(0, 0, 1, 1, 0, 1, ((0, 1),), (0,))]


def _ring() -> Padic:
    return Padic(3, modulus_polynomial(3), 4)


def test_target_row_cap_counts_union_not_per_mode() -> None:
    modes = _modes()
    assert target_packet_row_caps(modes, (0, 1), 0) == {0: 1}
    assert target_packet_row_caps(modes, (0, 1), 1) == {}
    assert passes_packet_row_caps(modes, (0, 1), (1, 0), 0)
    assert not passes_packet_row_caps(modes, (0, 1), (1, 1), 0)
    assert passes_packet_row_caps(modes, (0, 1), (1, 1), 1)
    with pytest.raises(ValueError):
        passes_packet_row_caps(modes, (0, 1), (1, -1), 0)


def test_hall_constraint_can_be_stricter_than_total_packet_cap() -> None:
    modes = [Mode(0, j, j, 2, 0, 1, (), rows) for j, rows in enumerate(
        ((0,), (0,), (1, 2)))]
    assert passes_packet_row_caps(modes, (0, 1, 2), (1, 1, 0), 0)
    assert not hall_packet_rows_possible(modes, (0, 1, 2), (1, 1, 0), 0)
    assert hall_packet_rows_possible(modes, (0, 1, 2), (1, 0, 1), 0)
    with pytest.raises(ValueError, match='work allowance'):
        hall_packet_rows_possible(modes, (0, 1, 2), (1, 0, 1), 0,
                                  max_occurrences=1)


def test_source_group_multiplicity_is_not_restricted_by_target_rows() -> None:
    modes = _modes()
    assert hall_packet_rows_possible(modes, (0, 1), (1, 1), 1)
    assert not hall_packet_rows_possible(modes, (0, 1), (1, 1), 0)


def test_row_capped_generator_avoids_false_raw_domain_refusal() -> None:
    modes = _modes()
    ring = _ring()
    stats = Counters()
    budget = ModeBudget(stats=stats, max_states=3, max_operations=1000)
    builder = FactorBuilder(modes=modes, factor_scopes={0: (0, 1)},
                            domains=(range(2), range(2)), ring=cast(NestedRing, ring), stats=stats,
                            evaluate_child=lambda *_: ring.one, budget=budget,
                            packet_row_caps=True)
    actual = tuple(builder.row_capped_assignments((0, 1), 'test', 0))
    assert actual == ((0, 0), (0, 1), (1, 0))
    with pytest.raises(CapacityError, match='factor size limit'):
        tuple(builder.row_capped_assignments((0, 1), 'source', 1))



@pytest.mark.parametrize('join', ('sparse', 'enumerate'))
@pytest.mark.parametrize('split_scopes', (False, True))
def test_opt_in_pruning_matches_full_exact_factor_algebra(
    join: Literal["sparse", "enumerate"], split_scopes: bool,
) -> None:
    modes = _modes()
    R = _ring()
    groups = {0, 1}
    scopes = ({(0, 0): (0, 1), (1, 0): (0, 1)} if split_scopes else None)

    def run(*, enable: bool, children: int) -> tuple[tuple[int, ...], int]:
        calls = 0
        def child(group: int | tuple[int, int], scope: tuple[int, ...],
                  assignment: tuple[int, ...]) -> tuple[int, ...]:
            nonlocal calls
            calls += 1
            g = group if isinstance(group, int) else group[0]
            if g == 0 and sum(assignment) > 1:
                return R.zero
            return R.one

        result = ModeEliminator(
            modes, groups, R, child, Counters(), CapacityError,
            factor_scopes=scopes, join_strategy=join, native_sparse=False,
            limits=ModeLimits(max_factor_states=4, max_child_contractions=children),
            packet_row_caps=enable,
        ).run()
        return cast(tuple[int, ...], result), calls

    got, requests = run(enable=True, children=7)
    assert got == R.scalar(3)
    assert requests == 7
    with pytest.raises(CapacityError, match='child-contraction limit'):
        run(enable=False, children=7)
    plain, requests_plain = run(enable=False, children=8)
    assert plain == got
    assert requests_plain == 8


def test_real_packet_entry_has_zero_coefficient_beyond_available_rows() -> None:
    net = simple_network(4,
        [([j], {(0,): 1, (1,): 1}) for j in range(4)],
        [([j], {(0,): 1, (1,): 1}) for j in range(4)])
    labels = (tuple(((j & 1), 0) for j in range(4)),
              tuple(((1 - (j & 1)), 0) for j in range(4)))
    packing = pack(net, 64, 2, labels)
    R = Padic(3, modulus_polynomial(3), 12)
    modes = mode_catalog(net, packing, 1, 12)
    target = [m for m in modes if m.packet == 0 and m.target == 0]
    assert len(target) >= 3
    assert len(target[0].rows) == 2
    assert all(m.weight >= packing.a + 1 + m.b for m in modes)
    for chosen in ((target[0], target[1], target[2]),):
        ctx = EvaluationContext(1, R.zero, R, packing.a)
        child = make_child(net, packing, list(chosen), (1, 1, 1), 1,
                           R.zero, R, 0, 0, ctx)
        entries = [vertex.oracle for vertex in child.right
                   if isinstance(vertex.oracle, PacketEntry)]
        assert len(entries) == 1
        entry = entries[0]
        assert all(entry(bits, R) == R.zero
                   for bits in product((0, 1), repeat=len(child.right[0].ports)))


def test_reference_enumeration_checks_both_weight_and_hall() -> None:
    modes = [Mode(0, j, j, 2, 0, 1, (), rows) for j, rows in enumerate(
        ((0,), (0,), (1, 2)))]
    supported = brute_row_capped_assignments(modes, 4, [0])
    assert (1, 1, 0) not in supported
    assert (1, 0, 1) in supported
    assert all(sum(m.weight * b for m, b in zip(modes, beta)) < 4
               for beta in supported)
    with pytest.raises(ValueError, match='Cartesian'):
        brute_row_capped_assignments(modes, 4, [0], max_cartesian=1)


@pytest.mark.parametrize('u', (8, 16, 32))
def test_admitted_uniform_packet_geometry_still_has_many_row_feasible_modes(u: int) -> None:
    witness = uniform_paper_row_capacity_witness(131072 * u)
    s = 1 << witness.lambda_bits
    assert witness.crossed_packets == (63 * s // 64) // witness.slots
    assert witness.chosen_mode_exponents_per_packet <= witness.per_packet_target_rows
    assert witness.maximum_subset_weight < witness.center_precision
    assert witness.subset_bits > 0
    # Constructively many β in {0,1} obey *all* packet-row Hall conditions.
    # The lower bound is Omega(s/sqrt(lambda)), not a solver-time lower bound.
    assert 128 * (isqrt(u) + 1) * witness.subset_bits >= s
    assert witness.subset_bits < s


def test_row_capacity_witness_rejects_inactive_paper_regime() -> None:
    with pytest.raises(ValueError, match='u>=8'):
        uniform_paper_row_capacity_witness(131072)


def test_actual_source_mode_elimination_prunes_only_zero_packet_terms() -> None:
    net = simple_network(4,
        [([j], {(0,): 1, (1,): 1}) for j in range(4)],
        [([j], {(0,): 1, (1,): 1}) for j in range(4)])
    labels = (tuple(((j & 1), 0) for j in range(4)),
              tuple(((1 - (j & 1)), 0) for j in range(4)))
    packing = pack(net, 64, 2, labels)
    R = Padic(3, modulus_polynomial(3), 12)
    modes = mode_catalog(net, packing, 1, R.p)
    independent = independently_evaluate_F(net, packing, 1, R.zero, R)
    results: list[tuple[int, ...]] = []
    calls: list[int] = []
    for enforce in (False, True):
        requests = 0
        context = EvaluationContext(1, R.zero, R, packing.a)
        def child(group: int | tuple[int, int], scope: tuple[int, ...],
                  assignment: tuple[int, ...]) -> tuple[int, ...]:
            nonlocal requests
            requests += 1
            g = group if isinstance(group, int) else group[0]
            network = make_child(net, packing, [modes[j] for j in scope],
                                 assignment, 1, R.zero, R, g, 0, context)
            return cast(tuple[int, ...], network.direct(R, network.edges))
        result = ModeEliminator(
            modes, {0, 1}, R, child, Counters(), CapacityError,
            native_sparse=False, join_strategy='sparse', packet_row_caps=enforce,
            limits=ModeLimits(max_factor_states=500, max_child_contractions=1000),
        ).run()
        results.append(cast(tuple[int, ...], result))
        calls.append(requests)
    assert results == [independent, independent]
    assert calls == [168, 162]


def test_iterative_row_capped_enumerator_matches_independent_small_cases() -> None:
    rng = random.Random(8007)
    for _ in range(70):
        p = rng.randrange(2, 9)
        modes: list[Mode] = []
        for j in range(rng.randrange(1, 6)):
            rows = tuple(k for k in range(3) if rng.randrange(2))
            modes.append(Mode(rng.randrange(3), j, j, 1, rng.randrange(2),
                              rng.randrange(1, 5), (), rows))
        domains = tuple(range(min(len(m.rows), (p - 1) // m.weight) + 1)
                        for m in modes)
        R = Padic(3, modulus_polynomial(3), p)
        budget = ModeBudget(stats=Counters(), max_states=10000,
                            max_operations=200000)
        builder = FactorBuilder(
            modes=modes, factor_scopes={0: tuple(range(len(modes)))},
            domains=domains, ring=cast(NestedRing, R), stats=Counters(),
            evaluate_child=lambda *_: R.one, budget=budget, packet_row_caps=True,
        )
        actual = tuple(builder.row_capped_assignments(tuple(range(len(modes))),
                                                      'differential', 0))
        expected = tuple(beta for beta in product(*domains)
                         if sum(mode.weight * b for mode, b in zip(modes, beta)) < p
                         and passes_packet_row_caps(
                             modes, tuple(range(len(modes))), beta, 0))
        assert set(actual) == set(expected)
        assert len(actual) == len(expected)


def test_hall_reference_matches_independent_small_exact_matching() -> None:
    def independently_match(rows: tuple[tuple[int, ...], ...],
                            i: int = 0, used: frozenset[int] = frozenset()) -> bool:
        if i == len(rows):
            return True
        return any(independently_match(rows, i + 1, used | {r})
                   for r in rows[i] if r not in used)

    neighborhoods = [tuple(r for r in range(3) if mask & (1 << r))
                     for mask in range(1, 8)]
    for selected in product(neighborhoods, repeat=3):
        modes = [Mode(0, j, j, 1, 0, 1, (), r)
                 for j, r in enumerate(selected)]
        for beta in product((0, 1, 2), repeat=3):
            requested = tuple(row for j, n in enumerate(beta)
                              for row in [selected[j]] * n)
            assert hall_packet_rows_possible(modes, (0, 1, 2), beta, 0) == (
                independently_match(requested))
