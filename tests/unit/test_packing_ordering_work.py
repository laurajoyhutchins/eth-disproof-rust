"""Falsification checks for the real packing and factor-order source loops."""
from __future__ import annotations

from random import Random

import pytest

from non_exponential_sudoku.core.network import Network, Vertex, TensorRing
from non_exponential_sudoku.core.lazy_coefficients import NestedCoords
from non_exponential_sudoku.core.packing import audit_packing, balanced_labels, pack
from non_exponential_sudoku.elimination.factors import Factor
from non_exponential_sudoku.elimination.ordering import select_variable
from non_exponential_sudoku.runtime.budget import ModeBudget
from non_exponential_sudoku.runtime.statistics import Counters
from reference.packing_ordering_work import (
    mode_ordering_work, packing_source_work,
)

pytestmark = pytest.mark.checkpoint


def make_graph(M: int, nl: int, nr: int, *, seed: int) -> Network:
    rng = Random(seed)
    left_ports: list[list[int]] = [[] for _ in range(nl)]
    right_ports: list[list[int]] = [[] for _ in range(nr)]
    for e in range(M):
        left_ports[rng.randrange(nl)].append(e)
        right_ports[rng.randrange(nr)].append(e)

    def one(bits: tuple[int, ...], ring: TensorRing) -> NestedCoords:
        return ring.one

    net = Network(
        [Vertex(f'L{i}', tuple(ports), one) for i, ports in enumerate(left_ports)],
        [Vertex(f'R{i}', tuple(ports), one) for i, ports in enumerate(right_ports)],
        M,
    )
    net.validate()
    return net


@pytest.mark.parametrize('M,nl,nr,r,a', [
    (0, 1, 1, 2, 2), (1, 1, 1, 2, 2), (4, 2, 3, 2, 2),
    (9, 4, 5, 3, 2), (16, 9, 11, 2, 3), (24, 8, 15, 4, 2),
    (20, 12, 10, 2, 2), (30, 20, 23, 3, 1),
])
@pytest.mark.parametrize('tie_break', ['spread', 'numeric'])
def test_packing_source_bound_on_real_graphs(
    M: int, nl: int, nr: int, r: int, a: int, tie_break: str,
) -> None:
    net = make_graph(M, nl, nr, seed=M + nl * 13 + nr * 19)
    work = packing_source_work(edges=M, vertices=nl+nr, groups=r, coordinates=a)
    labels = balanced_labels(net, r, a, tie_break=tie_break)  # type: ignore[arg-type]
    packing = pack(net, r, a, labels)
    audit = audit_packing(net, packing)
    assert audit['all_edges_packed_exactly_once']
    assert audit['orientation_geometry_valid']
    assert len(packing.packets) <= work.maximum_packet_count
    assert sum(len(p.slots) for p in packing.packets) <= work.maximum_allocated_packet_slots
    assert all(len(p.slots) == work.slots for p in packing.packets)
    assert len(labels[0]) + len(labels[1]) == work.vertices
    assert all(len(lbl) == a and all(0 <= d < r for d in lbl)
               for side in labels for lbl in side)


def test_symbolic_packing_bound_does_not_enumerate_full_label_alphabet() -> None:
    work = packing_source_work(edges=300, vertices=601, groups=64, coordinates=96)
    assert work.full_label_bits < 2000
    assert work.maximum_packet_count == 300 * (300 + (1 << 96))
    assert work.abstract_schoolbook_bit_work > work.maximum_allocated_packet_slots
    assert work.abstract_schoolbook_bit_work.bit_length() < 1200


@pytest.mark.parametrize('order', ['min_fill', 'min_states'])
def test_ordering_work_on_real_overlapping_factor_scopes(order: str) -> None:
    # No claim about the optimal elimination width. Only verify that the
    # exact source ordering works with bounded-domain, polynomial-bit scores.
    scopes = ((0, 1, 2), (2, 3), (3, 4), (0, 4))
    m, p = 5, 7
    live = [Factor(s, {}) for s in scopes]
    remaining = set(range(m))
    domains = tuple(range((j % 3) + 1) for j in range(m))
    bound = mode_ordering_work(variables=m, factors=len(live), precision=p)
    stats = Counters()
    budget = ModeBudget(stats=stats, max_operations=10**9)
    for _ in range(m):
        selected = select_variable(remaining, factors=live, domains=domains,
                                   order=order, stats=stats, budget=budget)  # type: ignore[arg-type]
        assert selected in remaining
        incident = [f for f in live if selected in f.scope]
        rest = [f for f in live if selected not in f.scope]
        union = set().union(*(f.scope for f in incident)) if incident else {selected}
        live = rest + [Factor(tuple(sorted(union - {selected})), {})]
        remaining.remove(selected)
        assert len(live) <= bound.maximum_live_factors
        for f in live:
            assert len(f.scope) <= m
    assert bound.selections == m
    assert bound.maximum_score_bits >= m
    assert budget.operations + budget.order_scans <= bound.abstract_schoolbook_bit_work


def test_ordering_scores_can_be_enormous_in_value_but_polynomial_in_bits() -> None:
    m, p = 400, 1 << 1024
    work = mode_ordering_work(variables=m, factors=800, precision=p)
    assert work.maximum_score_bits <= 400 * 1025 + 64
    assert work.abstract_schoolbook_bit_work.bit_length() < 180


@pytest.mark.parametrize('bad', [
    {'edges': -1, 'vertices': 3, 'groups': 64, 'coordinates': 2},
    {'edges': 1, 'vertices': 3, 'groups': 0, 'coordinates': 2},
    {'edges': 1, 'vertices': 3, 'groups': 64, 'coordinates': 0},
])
def test_packing_rejects_missing_positive_shape(bad: dict[str, int]) -> None:
    with pytest.raises(ValueError):
        packing_source_work(**bad)


@pytest.mark.parametrize('variables,factors,precision', [(-1, 1, 3), (1, -1, 3), (1, 1, 0)])
def test_ordering_rejects_invalid_shape(variables: int, factors: int, precision: int) -> None:
    with pytest.raises(ValueError):
        mode_ordering_work(variables=variables, factors=factors, precision=precision)


def test_real_packing_with_many_sparse_symbol_families_is_not_assumed_dense() -> None:
    net = make_graph(16, 16, 16, seed=8001)
    certificate = packing_source_work(edges=16, vertices=32, groups=5, coordinates=2)
    packed = pack(net, 5, 2)
    assert len(packed.packets) <= certificate.maximum_packet_count
    assert sum(len(p.slots) for p in packed.packets) <= certificate.maximum_allocated_packet_slots
    assert sum(sum(e is not None for e in p.slots) for p in packed.packets) == 16
    # No claim of a paper-admitted packing; padded families are charged.
    assert any(e is None for p in packed.packets for e in p.slots)
