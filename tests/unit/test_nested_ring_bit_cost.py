"""Research TDD for finite-ring bit-work and nested-value size envelopes.

Tests exercise independent operation counting and the genuine reference
arithmetic. They do not convert empirical counts to complexity theorems.
"""
from __future__ import annotations

from random import Random
from typing import Any, cast
from collections import Counter

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing, precision_ring, embed_element
from non_exponential_sudoku.core.lazy_coefficients import NestedCoords
from non_exponential_sudoku.runtime.config import ContractorConfig, RecoveryConfig
from reference.nested_ring_bit_cost import (
    bit_operation_envelope, canonical_cost_envelope, canonical_value,
    family_payload_envelope, UncertifiedRingInput,
)

pytestmark = pytest.mark.checkpoint


def _ring(q: tuple[int, ...] = (), e: int = 3, p: int = 7) -> Padic | JetRing:
    out: Padic | JetRing = Padic(e, modulus_polynomial(e), p)
    for length in q:
        out = JetRing(out, length)
    return out


def _dense_value(ring: Padic | JetRing, seed: int, unit: bool = False) -> NestedCoords:
    rng = Random(seed)
    if isinstance(ring, Padic):
        return tuple([rng.randrange(1 << ring.p) | 1] +
                     [rng.randrange(1 << ring.p) for _ in range(ring.e-1)]) if unit else (
                     tuple(rng.randrange(1 << ring.p) for _ in range(ring.e)))
    return tuple(_dense_value(cast(Padic | JetRing, ring.base), seed + 71 * (i + 1),
                              unit=(unit and i == 0)) for i in range(ring.q))


@pytest.mark.parametrize('lengths', [(), (1,), (2,), (2,3), (2,3,4)])
def test_value_payload_and_tree_node_formula_are_exact(lengths: tuple[int, ...]) -> None:
    ring = _ring(lengths, 3, 9)
    envelope = bit_operation_envelope(ring)
    coords, payload, nodes = family_payload_envelope(3, 9, lengths)
    assert (envelope.coordinate_count, envelope.canonical_payload_bits,
            envelope.tuple_nodes) == (coords, payload, nodes)
    value = _dense_value(ring, 17)
    assert canonical_value(ring, value)

    def visit(v: object) -> tuple[int, int]:
        if type(v) is not tuple:
            return (0, 1)
        children = [visit(x) for x in v]
        return (1 + sum(t for t, _ in children), sum(i for _, i in children))

    assert visit(value) == (nodes, coords)


def test_canonical_input_premise_rejects_arbitrary_big_int_and_wrong_shapes() -> None:
    ring = _ring((2,), 3, 9)
    assert canonical_value(ring, ring.one)
    value = ((1 << 10, 0, 0), ring.zero[1])
    assert not canonical_value(ring, value)
    assert not canonical_value(ring, ((1,0,0),))
    with pytest.raises(UncertifiedRingInput, match='canonical'):
        canonical_cost_envelope(ring, value)
    with pytest.raises(UncertifiedRingInput):
        canonical_cost_envelope(ring)
    with pytest.raises(ValueError):
        family_payload_envelope(3, 5, (2, 0))


def test_theorem_schedule_does_not_execute_nested_jet_arithmetic() -> None:
    with pytest.raises(ValueError, match='experimentally supported'):
        ContractorConfig(s=100, precision=17, schedule='paper',
                         recovery=RecoveryConfig(method='jet'))
    assert ContractorConfig(s=100, precision=17, schedule='paper').recovery.method == 'interpolate'


@pytest.mark.parametrize('lengths', [(), (2,), (2,3)])
def test_reference_arithmetic_maintains_canonical_sizes_and_precision(
    lengths: tuple[int, ...], monkeypatch: pytest.MonkeyPatch,
) -> None:
    import non_exponential_sudoku.core.algebra as algebra
    monkeypatch.setattr(algebra, '_native_ring', None)
    # Ring objects resolve Cython at creation time. Force actual Python
    # schoolbook arithmetic, whose recurrences we are modeling.
    import non_exponential_sudoku.core.jets as jets
    monkeypatch.setattr(jets, '_nr', None)
    ring = _ring(lengths, 3, 9)
    a = _dense_value(ring, 41, unit=True)
    b = _dense_value(ring, 93, unit=True)
    env = canonical_cost_envelope(ring, a, b)
    dynamic = cast(Any, ring)
    for out in [dynamic.add(a,b), dynamic.sub(a,b), dynamic.neg(a),
                dynamic.mul(a,b), dynamic.inv(a), dynamic.pow(a, 3), dynamic.pow(a, -2)]:
        assert canonical_value(ring, out)
    assert env.add_bits > 0 and env.mul_bits >= env.add_bits
    assert env.inv_bits >= env.mul_bits
    assert env.pow_bits(33) > env.pow_bits(3)
    assert env.pow_bits(-1) > env.pow_bits(1)
    upgraded = precision_ring(ring, 17)
    assert canonical_value(upgraded, embed_element(a, ring, upgraded))
    assert bit_operation_envelope(upgraded).canonical_payload_bits == env.coordinate_count * 17


@pytest.mark.parametrize('lengths', [(2,), (3,), (2,3)])
def test_nested_ring_call_recurrences_bound_real_dense_python_work(
    lengths: tuple[int, ...], monkeypatch: pytest.MonkeyPatch,
) -> None:
    import non_exponential_sudoku.core.algebra as algebra
    import non_exponential_sudoku.core.jets as jets
    monkeypatch.setattr(algebra, '_native_ring', None)
    monkeypatch.setattr(jets, '_nr', None)
    ring = _ring(lengths, 3, 11)
    assert isinstance(ring, JetRing)
    base = cast(Padic | JetRing, ring.base)
    rng = Random(102)

    def random_value(r: Padic | JetRing) -> object:
        if isinstance(r, Padic):
            return tuple(rng.randrange(1 << r.p) for _ in range(r.e))
        return tuple(random_value(cast(Padic | JetRing, r.base)) for _ in range(r.q))

    a = random_value(ring)
    b = random_value(ring)
    observed: Counter[str] = Counter()
    original_mul = type(base).mul
    original_add = type(base).add

    def multiply(self: object, x: object, y: object) -> object:
        if self is base:
            observed['mul'] += 1
        return cast(Any, original_mul)(self, x, y)

    def add(self: object, x: object, y: object) -> object:
        if self is base:
            observed['add'] += 1
        return cast(Any, original_add)(self, x, y)

    monkeypatch.setattr(type(base), 'mul', multiply)
    monkeypatch.setattr(type(base), 'add', add)
    cast(Any, ring).mul(a,b)
    q = lengths[-1]
    assert observed['mul'] <= q * (q + 1) // 2
    assert observed['add'] <= q * (q + 1) // 2


def test_bit_model_monotone_in_precision_and_nesting() -> None:
    p1 = bit_operation_envelope(_ring((), 3, 7))
    p2 = bit_operation_envelope(_ring((), 3, 21))
    j1 = bit_operation_envelope(_ring((2,), 3, 21))
    j2 = bit_operation_envelope(_ring((2,3), 3, 21))
    for a,b in ((p1,p2),(p2,j1),(j1,j2)):
        assert b.canonical_payload_bits >= a.canonical_payload_bits
        assert b.mul_bits >= a.mul_bits
        assert b.inv_bits >= a.inv_bits
        assert b.temporary_payload_bits >= a.temporary_payload_bits


def test_precise_scalar_coordinate_growth_is_not_a_runtime_allocation_claim() -> None:
    e, p = 4, 40
    dimensions = (3, 5, 7)
    coords, payload, nodes = family_payload_envelope(e,p,dimensions)
    assert coords == 4*3*5*7
    assert payload == coords * p
    assert nodes == 1 + 7 + 7*5 + 7*5*3
    # Avoid treating this as observed RSS or factor-table retention.
    assert nodes < coords


def test_inversion_recurrence_bounds_base_ring_operations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Verify the precise quadratic triangular-loop counts, not timing."""
    import non_exponential_sudoku.core.algebra as algebra
    import non_exponential_sudoku.core.jets as jets

    monkeypatch.setattr(algebra, '_native_ring', None)
    monkeypatch.setattr(jets, '_nr', None)
    ring = _ring((5,), 3, 11)
    assert isinstance(ring, JetRing)
    base = cast(Padic, ring.base)
    value = _dense_value(ring, 300, unit=True)
    counts: Counter[str] = Counter()
    for op in ('mul', 'add', 'neg', 'inv'):
        original = getattr(Padic, op)

        def counter(self: Padic, *args: object, _op: str = op,
                    _original: Any = original) -> Any:
            if self is base:
                counts[_op] += 1
            return _original(self, *args)

        monkeypatch.setattr(Padic, op, counter)
    output = ring.inv(cast(Any, value))
    assert canonical_value(ring, output)
    q = ring.q
    assert counts['inv'] == 1
    # The Padic base inverse itself performs Newton-lift multiplications.
    # A ring-call tracer observes those too: they must not be free.
    inverse_newton_mul = 2 * (base.p.bit_length() + 1) + 1
    assert counts['mul'] <= q * (q - 1) // 2 + (q - 1) + inverse_newton_mul
    assert counts['add'] <= q * (q - 1) // 2
    assert counts['neg'] == q - 1
    assert ring.mul(cast(Any, value), output) == ring.one


def test_symbolic_cost_formula_matches_constructed_ring_without_native() -> None:
    from reference.nested_ring_bit_cost import finite_shape_bit_envelope

    for precision in (3, 9, 33):
        for lengths in ((), (2,), (2, 3)):
            assert finite_shape_bit_envelope(3, precision, lengths) == (
                bit_operation_envelope(_ring(lengths, 3, precision))
            )


def test_paper_padic_bit_envelopes_use_only_interpolation_precisions() -> None:
    from reference.nested_ring_bit_cost import paper_padic_bit_envelopes
    from reference.precision_envelope import paper_frame_envelopes

    # Active paper schedule. The model never calls modulus_polynomial(e)
    # for the enormous e=4*lambda; it operates on exact shape integers.
    s = (1 << 131071) + 1
    cfg = ContractorConfig(s=s, precision=33, schedule='paper')
    frames = paper_frame_envelopes(cfg, edges=s, vertices=s)
    estimates = paper_padic_bit_envelopes(cfg, edges=s, vertices=s)
    assert len(estimates) == len(frames)
    assert any(not frame.terminal for frame in frames)
    for frame, estimate in zip(frames, estimates):
        assert estimate.jet_lengths == ()
        assert estimate.extension_degree == 4 * (s - 1).bit_length()
        assert estimate.precision == frame.child_precision
        assert estimate.canonical_payload_bits == estimate.extension_degree * frame.child_precision
        assert estimate.mul_bits > estimate.add_bits
    with pytest.raises(ValueError, match='paper schedule'):
        paper_padic_bit_envelopes(ContractorConfig(s=8, precision=5, schedule='micro'),
                                  edges=4, vertices=3)
