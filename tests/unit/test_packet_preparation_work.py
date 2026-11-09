"""Independent operation tracing and adversarial child-preparation contracts.

Only the *construction* is charged here, never a child contraction.
"""
from __future__ import annotations

from collections import Counter
from itertools import product

import pytest

from non_exponential_sudoku.contraction.children import make_child
from non_exponential_sudoku.contraction.compiled_children import CompiledChildPlan
from non_exponential_sudoku.contraction.packets import EvaluationContext, PacketEntry
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.sudoku.encoding import port_graph_with_cross_mode
from reference.packet_preparation_work import (
    CROSS_MISS_CALLS, RingCalls, UncertifiedPreparation,
    cauchy_context_calls, prepared_child_work,
)

pytestmark = pytest.mark.checkpoint


class CountedRing:
    """Transparent counter around the *actual* Padic arithmetic methods."""

    def __init__(self, ring: Padic) -> None:
        self.ring = ring
        self.calls: Counter[str] = Counter()

    def __getattr__(self, key: str) -> object:
        attr = getattr(self.ring, key)
        if key not in ('scalar', 'add', 'mul', 'inv', 'pow', 'sub', 'neg'):
            return attr

        def invoke(*args: object) -> object:
            self.calls[key] += 1
            return attr(*args)
        return invoke


def calls_after(before: Counter[str], after: Counter[str]) -> RingCalls:
    return RingCalls(**{key: after[key] - before[key]
                        for key in ('scalar', 'add', 'mul', 'inv', 'pow')})


@pytest.mark.parametrize('a', [1, 2, 3])
@pytest.mark.parametrize('t_sign', [-1, 1])
def test_real_cauchy_context_calls_match_source_exactly(a: int, t_sign: int) -> None:
    ring = CountedRing(Padic(5, modulus_polynomial(5), 13))
    context = EvaluationContext(t_sign, ring.one, ring, a)  # type: ignore[arg-type]
    assert context.cauchy[t_sign] is not None
    assert calls_after(Counter(), ring.calls) == cauchy_context_calls(1 << a)


@pytest.mark.parametrize('a', [1, 2, 3])
def test_cross_mode_first_miss_and_cached_hit(a: int) -> None:
    ring = CountedRing(Padic(5, modulus_polynomial(5), 15))
    context = EvaluationContext(1, ring.one, ring, a)  # type: ignore[arg-type]
    first = ring.calls.copy()
    result = context.cross_coefficient(0, 0, 3)
    assert calls_after(first, ring.calls) == CROSS_MISS_CALLS
    before_hit = ring.calls.copy()
    assert context.cross_coefficient(0, 0, 3) == result
    assert ring.calls == before_hit
    context.cross_coefficient(0, 0, 2)
    assert calls_after(before_hit, ring.calls) == CROSS_MISS_CALLS


def test_actual_direct_child_preparation_fits_count_and_compiled_oracles_agree() -> None:
    source = port_graph_with_cross_mode()
    packing = pack(source, 2, 1, (((0,),), ((1,),)))
    p = 9
    ring = Padic(5, modulus_polynomial(5), p)
    modes = mode_catalog(source, packing, 1, p)
    assert modes
    shape = prepared_child_work(
        edges=source.edges, vertices=len(source.left) + len(source.right),
        packets=len(packing.packets), slots=1 << packing.a, modes=len(modes),
        precision=p, extension_degree=ring.e,
        input_name_bits=sum(8 * len(v.name) for v in source.left + source.right),
    )
    assert shape.preparation_ring_calls.inv == shape.cross_misses
    assert shape.mode_count_limit >= len(modes)
    assert len(modes) <= shape.mode_count_limit
    assert sum(len(m.tile) + len(m.rows) for m in modes) <= (
        2 * shape.slots * shape.mode_count_limit)
    assert shape.catalog_index_visits >= 2 * source.edges
    # Two distinct assignments exercise both inactive and active target modes.
    for beta in (tuple(0 for _ in modes), tuple(1 for _ in modes)):
        for group in (0, 1):
            counted = CountedRing(ring)
            ctx = EvaluationContext(1, counted.one, counted, packing.a)  # type: ignore[arg-type]
            before = counted.calls.copy()
            direct = make_child(
                source, packing, modes, beta, 1, counted.one,
                counted, group, 0, ctx,  # type: ignore[arg-type]
            )
            ring_calls = calls_after(before, counted.calls)
            ceiling = shape.preparation_ring_calls
            for operation in ('scalar', 'add', 'mul', 'inv', 'pow'):
                assert getattr(ring_calls, operation) <= getattr(ceiling, operation)
            assert direct.edges <= 2 * source.edges
            assert len(direct.right) <= len(packing.packets)
            for node in direct.right:
                assert isinstance(node.oracle, PacketEntry)
                assert len(node.oracle.geometry.rows) <= shape.slots
                assert len(node.oracle.terms.target) <= len(modes)
                assert len(node.oracle.terms.source) <= len(modes)
                assert sum(len(v) for v in node.oracle.terms.contributions.values()) <= (
                    shape.slots * len(modes))
            planned = CompiledChildPlan(source, packing, group, 0)
            compiled = planned.instantiate(modes, beta, 1, ring.one, ring,
                                           EvaluationContext(1, ring.one, ring, packing.a))
            assert direct.edges == compiled.edges
            assert [v.ports for v in direct.left] == [v.ports for v in compiled.left]
            assert [v.ports for v in direct.right] == [v.ports for v in compiled.right]
            for a_node, b_node in zip(direct.right, compiled.right):
                for assignment in product((0, 1), repeat=len(a_node.ports)):
                    assert a_node.oracle(assignment, counted) == b_node.oracle(assignment, ring)  # type: ignore[arg-type]


def test_mode_catalog_and_zero_cross_modes_cannot_create_unbounded_work() -> None:
    x = prepared_child_work(edges=30, vertices=40, packets=8, slots=4,
                            modes=0, precision=3, extension_degree=5,
                            input_name_bits=80)
    assert x.cross_misses == 0
    assert x.preparation_ring_calls == RingCalls()
    assert x.center_ring_calls == cauchy_context_calls(4)
    assert x.schoolbook_bit_work_majorant > 0
    assert x.abstract_index_visits >= x.packets * x.slots**2


def test_symbolic_paper_preparation_is_polynomial_given_precision_and_metadata() -> None:
    # These are symbolic shape inputs. The paper is inactive for constructible
    # networks at these sizes; no claim that this materializes an admitted one.
    for k in (1, 2, 4, 8):
        s = 2 ** (4*k + 8)
        L = 2**k
        P = s // L
        p = s + 7
        m = P * L * (p - 1)  # maximal mode catalog, intentionally enormous
        result = prepared_child_work(edges=s, vertices=2*s, packets=P,
                                     slots=L, modes=m, precision=p,
                                     extension_degree=4*(s.bit_length()),
                                     input_name_bits=64*s)
        assert result.mode_count_limit == m
        assert result.cross_misses == P * L * m
        assert result.prepared_payload_bits <= (2*L+result.cross_misses) * result.extension_degree * p
        assert result.schoolbook_bit_work_majorant > result.abstract_index_visits


@pytest.mark.parametrize('bad', [
    {'slots': 3}, {'packets': 31}, {'modes': 1000},
    {'precision': 0}, {'extension_degree': 1}, {'input_name_bits': -1},
])
def test_unproved_shapes_refused_instead_of_zero_cost(bad: dict[str, int]) -> None:
    arguments = dict(edges=20, vertices=30, packets=10, slots=2,
                     modes=10, precision=5, extension_degree=5,
                     input_name_bits=100)
    with pytest.raises(UncertifiedPreparation):
        prepared_child_work(**(arguments | bad))
