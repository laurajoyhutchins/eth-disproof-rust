"""Packet values and bounded caches belong to one deformation center."""
from __future__ import annotations

import pytest

from non_exponential_sudoku.contraction.compiled_children import CompiledChildPlan
from non_exponential_sudoku.contraction.packets import BoundedPacketMemo, EvaluationContext
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.packing import pack
from reference.sudoku_network_oracle import port_graph_with_cross_mode

pytestmark = pytest.mark.checkpoint


def test_packet_memo_lru_has_both_entry_and_byte_bounds() -> None:
    ring = Padic(5, modulus_polynomial(5), 13)
    memo = BoundedPacketMemo(ring, entries=2, max_bytes=4096)
    value = ring.one
    missing = memo.get(('a',))
    assert missing is not value
    memo.put(('a',), value)
    memo.put(('b',), value)
    assert memo.get(('a',)) == value  # 'a' is now the newest entry.
    memo.put(('c',), value)
    assert memo.get(('b',)) is not value
    assert (memo.hits, memo.misses, memo.evictions) == (1, 2, 1)
    assert memo.live_bytes <= memo.max_bytes
    assert memo.peak_bytes <= memo.max_bytes

    # A single entry that exceeds the budget must disable caching entirely.
    context = EvaluationContext(1, ring.one, ring, 1,
                                packet_memo_entries=16, packet_memo_bytes=1)
    assert context.memo is None


def test_packet_memo_never_outlives_its_deformation_center() -> None:
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    ring = Padic(5, modulus_polynomial(5), 13)
    modes = mode_catalog(net, packing, 1, ring.p)
    assignment = (0,) * len(modes)
    plan = CompiledChildPlan(net, packing, 0, 0)

    def evaluate(context: EvaluationContext) -> tuple[int, ...]:
        child = plan.instantiate(modes, assignment, 1, ring.one, ring, context)
        assert child.right
        packet = child.right[0]
        bits = (0,) * len(packet.ports)
        expected = packet.oracle(bits, ring)
        assert packet.oracle(bits, ring) == expected
        return expected

    first = EvaluationContext(1, ring.one, ring, 1,
                              packet_memo_entries=16, packet_memo_bytes=8192)
    second = EvaluationContext(1, ring.one, ring, 1,
                               packet_memo_entries=16, packet_memo_bytes=8192)
    assert evaluate(first) == evaluate(second)
    assert first.memo is not None and second.memo is not None
    assert (first.memo.hits, first.memo.misses) == (1, 1)
    assert (second.memo.hits, second.memo.misses) == (1, 1)
