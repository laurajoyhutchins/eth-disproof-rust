"""Exactness checks for reusable leaf schedules and compiled packet slots."""
from __future__ import annotations

import random
from itertools import product

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.network import (
    compile_leaf_plan, eliminate_leaf, simple_network,
)
from non_exponential_sudoku.contraction.children import compile_child, make_child
from non_exponential_sudoku.contraction.packets import PacketEntry, PacketGeometry
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def test_packet_geometry_is_immutable_even_when_the_input_maps_are_not():
    ports = {("Y", 0): 0}
    slots = {11: 0}
    geometry = PacketGeometry(ports, (0,), ((0, 0),), (), (), slots)
    ports[("Y", 0)] = 3
    slots[11] = 7
    assert geometry.port_map[("Y", 0)] == 0
    assert geometry.slot_for_edge[11] == 0
    with pytest.raises(TypeError):
        geometry.port_map[("Y", 0)] = 4
    with pytest.raises(TypeError):
        geometry.slot_for_edge[11] = 2


def _partition(rng, edges):
    groups = []
    for edge in range(edges):
        if groups and rng.randrange(3):
            groups[rng.randrange(len(groups))].append(edge)
        else:
            groups.append([edge])
    return groups


@pytest.mark.parametrize('q', [None, 3])
def test_leaf_plan_matches_direct_and_uncompiled_for_random_factors(q):
    rng = random.Random(19001 + (q or 0))
    base = Padic(3, modulus_polynomial(3), 17)
    ring = JetRing(base, q) if q else base
    for _ in range(45):
        edges = rng.randint(1, 6)
        sides = []
        for _ in range(2):
            parts = _partition(rng, edges)
            sides.append([
                (ports, {bits: rng.choice((-3, -1, 0, 1, 2, 7))
                         for bits in product((0, 1), repeat=len(ports))})
                for ports in parts
            ])
        net = simple_network(edges, *sides)
        scopes = tuple(v.ports for v in net.left + net.right)
        plan = compile_leaf_plan(edges, scopes)
        assert plan is not None
        expected = net.direct(ring, 6)
        assert eliminate_leaf(net, ring, 6, plan=plan) == expected
        assert eliminate_leaf(net, ring, 6) == expected


def test_leaf_plan_bounded_lookup_fallback_and_capacity():
    ring = Padic(3, modulus_polynomial(3), 7)
    net = simple_network(4,
        [([0, 1, 2, 3], {bits: 1 for bits in product((0, 1), repeat=4)})],
        [([0, 1], {(0, 0): 1, (1, 1): 1}),
         ([2, 3], {(0, 0): 1, (1, 1): 1})])
    scopes = tuple(v.ports for v in net.left + net.right)
    plan = compile_leaf_plan(net.edges, scopes, lookup_budget=0)
    assert plan is not None
    assert any(s.lookup is None for s in plan.steps)
    assert eliminate_leaf(net, ring, 4, plan=plan) == net.direct(ring, 4)
    assert compile_leaf_plan(net.edges, scopes, max_width=2) is None
    assert eliminate_leaf(net, ring, 4, max_width=2) == net.direct(ring, 4)
    with pytest.raises(ValueError, match='does not match'):
        eliminate_leaf(net, ring, 4, max_width=2, plan=plan)
    with pytest.raises(CapacityError, match='limit'):
        eliminate_leaf(net, ring, 3, plan=plan)


def test_precompiled_packet_bits_match_direct_implicit_packet_oracle():
    # Check packet geometry against the exact direct contraction, and check
    # empty-mode packets against an independently indexed Cauchy product.
    net = simple_network(3,
        [([0, 1], {(0, 0): 1, (1, 1): 1}),
         ([2], {(0,): 1, (1,): 1})],
        [([0, 2], {(0, 0): 1, (1, 1): 1}),
         ([1], {(0,): 1, (1,): 1})])
    packing = pack(net, 64, 2,
                   (((0, 0), (0, 0)), ((1, 0), (1, 0))))
    ring = Padic(5, modulus_polynomial(5), 9)
    modes = mode_catalog(net, packing, 1, ring.p)
    checked_cauchy = 0
    for group in (0, 1):
        plan = compile_child(net, packing, group, 0)
        for beta in ((0,) * len(modes), (1,) * len(modes)):
            child = make_child(net, packing, modes, beta, 1,
                               ring.basis(3), ring, group, 0, plan=plan)
            assert child.leaf_plan is plan.leaf_plan
            for vertex in child.right:
                oracle = vertex.oracle
                assert isinstance(oracle, PacketEntry)
                for bits in product((0, 1), repeat=len(vertex.ports)):
                    # An independently created no-plan entry must agree.
                    check = PacketEntry(net, packing, oracle.packet_id, group, 0,
                                        1, ring.basis(3), ring, modes, beta,
                                        oracle.geometry.port_map)
                    actual = oracle(bits, ring)
                    assert actual == check(bits, ring)
                    if not oracle.terms.target and not oracle.terms.source:
                        packet = packing.packets[oracle.packet_id]
                        left = {slot: bits[pos] for (side, slot), pos
                                in oracle.geometry.port_map.items() if side == 'Y'}
                        right = {slot: bits[pos] for (side, slot), pos
                                 in oracle.geometry.port_map.items() if side == 'X'}
                        expected = ring.one
                        for x in oracle.rows:
                            local = ring.zero
                            for y, edge in enumerate(packet.slots):
                                if edge is not None and right.get(y, 0):
                                    local = ring.add(local, oracle.cauchy[y - x])
                            expected = ring.mul(expected, local if left[x]
                                else ring.sub(ring.one, local))
                        assert actual == expected
                        checked_cauchy += 1
            assert eliminate_leaf(child, ring, 12, plan=child.leaf_plan) == child.direct(ring, 12)

    assert checked_cauchy > 0
