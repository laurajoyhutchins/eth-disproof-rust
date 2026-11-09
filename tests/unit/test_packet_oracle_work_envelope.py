"""Independent upper-envelope checks on real prepared packet oracles.

No timing assertions and no claim that outer ring calls bound bit operations.
"""
from __future__ import annotations

from collections import Counter
from itertools import product

import pytest

from non_exponential_sudoku.contraction.children import make_child
from non_exponential_sudoku.contraction.packets import EvaluationContext, PacketEntry
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.packing import pack
from reference.sudoku_network_oracle import port_graph_with_cross_mode
from reference.packet_oracle_work import (
    coefficient_payload_bits, coefficient_state_capacity, packet_evaluation_envelope,
)

pytestmark = pytest.mark.checkpoint


class RingCounter:
    def __init__(self, base: object) -> None:
        self.base = base
        self.counts: Counter[str] = Counter()

    def __getattr__(self, key: str) -> object:
        attribute = getattr(self.base, key)
        if key not in ('add', 'sub', 'neg', 'mul', 'scalar', 'pow'):
            return attribute

        def record(*args: object) -> object:
            self.counts[key] += 1
            return attribute(*args)
        return record


def test_capacity_product_is_symbolic_and_exposes_exponential_states() -> None:
    assert coefficient_state_capacity(()) == 1
    assert coefficient_state_capacity((2, 4, 0)) == 15
    assert coefficient_state_capacity((1,) * 128) == 1 << 128
    for invalid in ((-1,), (1.0,)):
        with pytest.raises(ValueError):
            coefficient_state_capacity(invalid)  # type: ignore[arg-type]


def test_coefficient_payload_scales_with_precision_and_nested_jet_layers() -> None:
    base = Padic(5, modulus_polynomial(5), 13)
    assert coefficient_payload_bits(base) == 65
    assert coefficient_payload_bits(JetRing(base, 3)) == 195
    assert coefficient_payload_bits(JetRing(JetRing(base, 2), 3)) == 390
    with pytest.raises(TypeError):
        coefficient_payload_bits(object())


@pytest.mark.parametrize('precision', [9, 15])
@pytest.mark.parametrize('nested', [False, True])
def test_actual_packet_ring_calls_fit_structural_envelope(
    precision: int, nested: bool,
) -> None:
    source = port_graph_with_cross_mode()
    packing = pack(source, 2, 1, (((0,),), ((1,),)))
    base = Padic(5, modulus_polynomial(5), precision)
    ring = JetRing(base, 2) if nested else base
    modes = mode_catalog(source, packing, 1, precision)
    assert modes
    assert len(modes) <= 10
    assignments = [(0,) * len(modes), (1,) * len(modes)]
    saw_mode = False
    for beta in assignments:
        context = EvaluationContext(1, ring.one, ring, 1)
        for group in (0, 1):
            child = make_child(source, packing, modes, beta, 1, ring.one, ring,
                               group, 0, context)
            for vertex in child.right:
                entry = vertex.oracle
                assert isinstance(entry, PacketEntry)
                envelope = packet_evaluation_envelope(entry)
                saw_mode |= bool(entry.terms.desired)
                assert envelope.coefficient_payload_bits == coefficient_payload_bits(ring)
                assert envelope.prepared_coefficient_payload_bits == (
                    envelope.prepared_coefficient_slots * envelope.coefficient_payload_bits
                )
                assert envelope.exponent_key_payload_bits >= envelope.target_modes
                assert len(vertex.ports) <= 6
                for bits in product((0, 1), repeat=len(vertex.ports)):
                    expected = entry._evaluate_python(bits)
                    counter = RingCounter(entry.work_ring)
                    entry.work_ring = counter  # type: ignore[assignment]
                    try:
                        actual = entry._evaluate_python(bits)
                    finally:
                        entry.work_ring = counter.base  # type: ignore[assignment]
                    assert actual == expected
                    for operation, max_calls in (
                        ('add', envelope.additions),
                        ('sub', envelope.subtractions),
                        ('neg', envelope.negations),
                        ('mul', envelope.multiplications),
                        ('scalar', envelope.scalar_constructions),
                        ('pow', envelope.powers),
                    ):
                        assert counter.counts[operation] <= max_calls, (operation, beta, bits)
    assert saw_mode


@pytest.mark.parametrize('target_count', range(1, 10))
def test_coefficient_table_can_have_exponential_transitions(
    target_count: int,
) -> None:
    """A legal *local table update* can realize every subset of target modes.

    This synthetic prepared descriptor is not claimed to be produced by a
    paper-admitted Sudoku packing. It witnesses the outer-loop algorithm's
    structural state explosion and motivates a separate reachability lemma.
    """
    from non_exponential_sudoku.contraction.packets import (
        PacketGeometry, PacketModeTerms,
    )

    from non_exponential_sudoku.core.modes import Mode
    ring = Padic(3, modulus_polynomial(3), 8)
    target = tuple((Mode(0, 0, 0, 0, 1, 1, (), (i,)), 1)
                   for i in range(target_count))
    # Each row either preserves its existing exponent tuple or advances a
    # fresh coordinate. Thus the number of states doubles at every row.
    row_terms = tuple((i, i, ((target_count, 0),)) for i in range(target_count))
    oracle = object.__new__(PacketEntry)
    oracle.R = ring
    oracle.work_ring = ring
    oracle.geometry = PacketGeometry({}, tuple(range(target_count)), (), (),
                                     row_terms, {})
    oracle.terms = PacketModeTerms(
        active=target, target=target, source=(), desired=(1,) * target_count,
        contributions={i: ((i, ring.one),) for i in range(target_count)},
        tile_slots=(), tile_bits=(),
    )
    oracle.cauchy = {0: ring.one}
    limit = packet_evaluation_envelope(oracle)
    counter = RingCounter(ring)
    oracle.work_ring = counter  # type: ignore[assignment]
    result = oracle._evaluate_python((1,) * (target_count + 1))
    assert result == ring.one
    assert counter.counts['mul'] == (1 << (target_count + 1)) - 2
    assert counter.counts['mul'] <= limit.multiplications
    assert limit.coefficient_states == 1 << target_count


def test_envelope_rejects_an_unmodelled_lazy_or_native_kernel() -> None:
    from non_exponential_sudoku.contraction.packets import PacketGeometry, PacketModeTerms
    ring = Padic(3, modulus_polynomial(3), 8)
    oracle = object.__new__(PacketEntry)
    oracle.R = ring
    oracle.work_ring = ring
    oracle.geometry = PacketGeometry({}, (), (), (), (), {})
    oracle.terms = PacketModeTerms((), (), (), (), {}, (), ())
    oracle.cauchy = {}
    oracle.native = object()  # type: ignore[assignment]
    with pytest.raises(TypeError, match='native packet'):
        packet_evaluation_envelope(oracle)
    oracle.native = None
    oracle.work_ring = object()  # type: ignore[assignment]
    with pytest.raises(TypeError, match='eager finite-ring'):
        packet_evaluation_envelope(oracle)
