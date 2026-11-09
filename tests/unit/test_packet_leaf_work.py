"""Source-correlated packet invocation bounds on real recursive child tensors.

The cost of original Sudoku entry oracles and of preparing packet terms is
separate. This suite checks invocation multiplicities for the eager Python
packet entry without treating them as a complete bit-time theorem.
"""
from __future__ import annotations

from collections import Counter
from itertools import product

import pytest

from non_exponential_sudoku.contraction.children import compile_child, make_child
from non_exponential_sudoku.contraction.packets import PacketEntry
from non_exponential_sudoku.contraction.zero_support import certify_zero
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.network import (
    Network, Vertex, compile_leaf_plan, eliminate_leaf, simple_network,
)
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.runtime.config import ZeroSupportPolicy
from reference.packet_leaf_work import (
    UncertifiedPacketLeaf, certify_packet_leaf_work,
)
from reference.packet_oracle_work import packet_evaluation_envelope

pytestmark = pytest.mark.checkpoint


def _root() -> Network:
    ones = {bits: 1 for bits in product((0, 1), repeat=2)}
    return simple_network(
        4,
        [([0, 1], ones), ([2, 3], ones)],
        [([0, 2], ones), ([1, 3], ones)],
    )


def _child(compiled: bool = False) -> tuple[Network, Padic]:
    net = _root()
    ring = Padic(3, modulus_polynomial(3), 9)
    packing = pack(net, 2, 1)
    group = packing.groups_left[0][0]
    plan = compile_child(net, packing, group, 0) if compiled else None
    child = make_child(net, packing, [], (), 1, ring.one, ring, group, 0, plan=plan)
    assert child.right
    assert all(isinstance(v.oracle, PacketEntry) for v in child.right)
    return child, ring


class CountingRing:
    def __init__(self, base: Padic) -> None:
        self.base = base
        self.calls: Counter[str] = Counter()

    def __getattr__(self, name: str) -> object:
        value = getattr(self.base, name)
        if name not in ("add", "sub", "neg", "mul", "scalar", "pow"):
            return value

        def count(*args: object) -> object:
            self.calls[name] += 1
            return value(*args)
        return count


@pytest.mark.parametrize("compiled", [False, True])
def test_real_child_direct_packet_calls_and_ring_work_fit_envelope(
    monkeypatch: pytest.MonkeyPatch, compiled: bool,
) -> None:
    child, ring = _child(compiled)
    bound = certify_packet_leaf_work(child, ring, leaf_strategy="enumerate")
    calls = [0]
    original = PacketEntry.__call__

    def counted(self: PacketEntry, bits: tuple[int, ...], target: object) -> object:
        calls[0] += 1
        return original(self, bits, target)  # type: ignore[arg-type]

    monkeypatch.setattr(PacketEntry, "__call__", counted)
    spies: list[CountingRing] = []
    original_rings: list[tuple[PacketEntry, object]] = []
    for v in child.right:
        entry = v.oracle
        assert isinstance(entry, PacketEntry)
        spy = CountingRing(ring)
        original_rings.append((entry, entry.work_ring))
        entry.work_ring = spy  # type: ignore[assignment]
        spies.append(spy)
    try:
        value = child.direct(ring, child.edges)
        assert isinstance(value, tuple)
    finally:
        for entry, work_ring in original_rings:
            entry.work_ring = work_ring  # type: ignore[assignment]
    assert 0 < calls[0] <= 1 << bound.direct_packet_calls_log2
    outer_calls = sum(sum(spy.calls.values()) for spy in spies)
    assert outer_calls <= 1 << bound.per_attempt_outer_ring_calls_log2
    assert bound.total_outer_ring_calls_log2 is None
    assert bound.universal_bit_bound_proven is False


@pytest.mark.parametrize("compiled", [False, True])
def test_factor_table_calls_are_bounded_and_agree_with_direct(
    monkeypatch: pytest.MonkeyPatch, compiled: bool,
) -> None:
    child, ring = _child(compiled)
    reference = child.direct(ring, child.edges)
    bound = certify_packet_leaf_work(child, ring, leaf_strategy="eliminate",
                                     potential_attempts_log2=3)
    counts: Counter[int] = Counter()
    original = PacketEntry.__call__

    def counted(self: PacketEntry, bits: tuple[int, ...], target: object) -> object:
        counts[id(self)] += 1
        return original(self, bits, target)  # type: ignore[arg-type]

    monkeypatch.setattr(PacketEntry, "__call__", counted)
    plan = compile_leaf_plan(
        child.edges, [v.ports for v in child.left + child.right if v.ports],
        max_width=8,
    ) if compiled else None
    assert eliminate_leaf(child, ring, child.edges, max_width=8, plan=plan) == reference
    for v in child.right:
        assert counts[id(v.oracle)] <= 1 << len(v.ports)
    assert sum(counts.values()) <= 1 << bound.dense_table_packet_calls_log2
    assert bound.total_outer_ring_calls_log2 == (
        3 + bound.per_attempt_outer_ring_calls_log2
    )
    assert bound.total_lift_coordinate_masks_log2 is not None


def test_zero_support_never_calls_packet_arithmetic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    child, ring = _child()
    bound = certify_packet_leaf_work(
        child, ring, zero_support=True,
    )
    assert bound.structural_support_rows_log2 > 0
    calls = [0]
    original = PacketEntry.__call__

    def counted(self: PacketEntry, bits: tuple[int, ...], target: object) -> object:
        calls[0] += 1
        return original(self, bits, target)  # type: ignore[arg-type]

    monkeypatch.setattr(PacketEntry, "__call__", counted)
    policy = ZeroSupportPolicy(
        enabled=True, max_child_edges=16, max_vertex_arity=16,
        max_support_rows=10_000,
    )
    result = certify_zero(child, ring, policy)
    assert result.verdict in ("zero", "possible", "unsupported")
    assert calls[0] == 0
    assert result.evaluated_rows <= sum(1 << len(v.ports) for v in child.left + child.right)


def test_direct_fallback_after_tables_charges_both_possible_paths() -> None:
    child, ring = _child()
    enumerated = certify_packet_leaf_work(child, ring, leaf_strategy="enumerate")
    eliminated = certify_packet_leaf_work(child, ring, leaf_strategy="eliminate")
    assert eliminated.per_attempt_packet_calls_log2 >= enumerated.per_attempt_packet_calls_log2
    assert eliminated.per_attempt_outer_ring_calls_log2 >= (
        enumerated.per_attempt_outer_ring_calls_log2
    )
    # The planned branch cannot invoke an oracle more often than one
    # complete factor table. The uncompiled branch may pay both tables
    # and a full direct fallback; neither is charged for free.
    assert eliminated.dense_table_packet_calls_log2 <= eliminated.per_attempt_packet_calls_log2


def test_lift_coefficient_masks_for_inherited_packet_are_charged(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    child, ring = _child()
    requested = Padic(ring.e, ring.f, ring.p + 3)
    bound = certify_packet_leaf_work(child, requested)
    assert bound.per_attempt_lift_coordinate_masks_log2 > 0
    scalar_lifts = [0]
    original = Padic.lift

    def counted(self: Padic, coords: object) -> tuple[int, ...]:
        scalar_lifts[0] += 1
        return original(self, coords)  # type: ignore[arg-type]

    monkeypatch.setattr(Padic, "lift", counted)
    child.direct(requested, child.edges)
    # Every Padic.lift visit masks e input coordinates.
    assert scalar_lifts[0] * ring.e <= (
        1 << bound.per_attempt_lift_coordinate_masks_log2
    )


def test_forged_packet_topology_and_unmodelled_kernel_fail_closed() -> None:
    child, ring = _child()
    packet = next(v for v in child.right if v.ports)
    packet_index = child.right.index(packet)
    entry = packet.oracle
    assert isinstance(entry, PacketEntry)
    corrupted = Network(list(child.left), list(child.right), child.edges)
    corrupted.right[packet_index] = Vertex(
        packet.name, packet.ports[:-1], entry,
    )
    # The parent incidence is no longer valid. Never silently certify.
    with pytest.raises((AssertionError, UncertifiedPacketLeaf)):
        certify_packet_leaf_work(corrupted, ring)
    entry.native = object()  # type: ignore[assignment]
    with pytest.raises(UncertifiedPacketLeaf, match="native/lazy"):
        certify_packet_leaf_work(child, ring)
    entry.native = None
    entry.work_ring = object()  # type: ignore[assignment]
    with pytest.raises(UncertifiedPacketLeaf, match="native/lazy"):
        certify_packet_leaf_work(child, ring)


def test_refuse_opaque_original_only_and_invalid_aggregate_assumptions() -> None:
    child, ring = _child()
    with pytest.raises(UncertifiedPacketLeaf, match="no generated"):
        certify_packet_leaf_work(_root(), ring)
    for bad in (-1, True, 1.2):
        with pytest.raises(ValueError):
            certify_packet_leaf_work(
                child, ring,
                potential_attempts_log2=bad,  # type: ignore[arg-type]
            )
    with pytest.raises(ValueError):
        certify_packet_leaf_work(child, ring, leaf_strategy="heuristic")  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        certify_packet_leaf_work(child, ring, zero_support=1)  # type: ignore[arg-type]
    expected = sum(packet_evaluation_envelope(v.oracle).ring_calls
                   for v in child.right if isinstance(v.oracle, PacketEntry))
    assert expected > 0

def test_second_generation_inherited_packet_is_charged_once_per_vertex(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = _root()
    ring = Padic(3, modulus_polynomial(3), 9)
    first_packing = pack(source, 2, 1)
    first = make_child(
        source, first_packing, [], (), 1, ring.one, ring,
        first_packing.groups_left[0][0], 0,
    )
    assert first.right
    second_packing = pack(first, 2, 1)
    second = make_child(
        first, second_packing, [], (), 1, ring.one, ring,
        second_packing.groups_right[0][0], 0,
    )
    assert any(isinstance(v.oracle, PacketEntry) for v in second.left)
    certificate = certify_packet_leaf_work(second, ring)
    assert certificate.packet_vertices == sum(
        isinstance(v.oracle, PacketEntry)
        for v in second.left + second.right
    )
    original_call = PacketEntry.__call__
    depth = [0, 0, 0]

    def traced(self: PacketEntry, bits: tuple[int, ...], target: object) -> object:
        depth[0] += 1
        depth[1] = max(depth[1], depth[0])
        depth[2] += 1
        try:
            return original_call(self, bits, target)  # type: ignore[arg-type]
        finally:
            depth[0] -= 1

    monkeypatch.setattr(PacketEntry, "__call__", traced)
    assert isinstance(second.direct(ring, second.edges), tuple)
    assert depth[1] == 1
    assert depth[2] > 0
    assert depth[2] <= 1 << certificate.direct_packet_calls_log2
    assert certificate.universal_bit_bound_proven is False

