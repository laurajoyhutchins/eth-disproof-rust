"""Exact direct-ring Cython dispatch with accounting and backend preservation."""
from __future__ import annotations

from itertools import product

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.network import compile_leaf_plan, simple_network
from non_exponential_sudoku.runtime.cost_ledger import CostLedger

pytestmark = [pytest.mark.checkpoint, pytest.mark.requires_native]


def _packet(ring, *, positions_are_bits=True):
    """Minimal Cauchy oracle with both add, sub and mul operations."""
    value = ring.scalar(3)
    return (ring, (0,), (((1, value),),), ((),), (), (), ((1, 1),))


def _run_packet(native, ring, bits=(0, 1)):
    args = _packet(ring)
    return native.packet_evaluate(bits, *args, positions_are_bits=True)


@pytest.mark.parametrize("jet_degree", (0, 3))
def test_direct_packet_ring_operations_skip_python_method_dispatch(
    jet_degree: int, monkeypatch: pytest.MonkeyPatch,
) -> None:
    native = pytest.importorskip("native_recursive")
    base = Padic(8, modulus_polynomial(8), 19)
    ring = JetRing(base, jet_degree) if jet_degree else base
    expected = _run_packet(native, ring)
    owner = JetRing if jet_degree else Padic

    def unexpected(*_args, **_kwargs):
        raise AssertionError("eligible native kernel called a Python ring method")

    with monkeypatch.context() as patch:
        patch.setattr(owner, "add", unexpected)
        patch.setattr(owner, "sub", unexpected)
        patch.setattr(owner, "mul", unexpected)
        assert _run_packet(native, ring) == expected


@pytest.mark.parametrize("jet_degree", (0, 3))
def test_observed_packet_keeps_ring_call_accounting(
    jet_degree: int, monkeypatch: pytest.MonkeyPatch,
) -> None:
    native = pytest.importorskip("native_recursive")
    base = Padic(8, modulus_polynomial(8), 19)
    ring = JetRing(base, jet_degree) if jet_degree else base
    expected = _run_packet(native, ring)
    owner = JetRing if jet_degree else Padic
    original = owner.mul
    calls = 0

    def counted_mul(self, a, b):
        nonlocal calls
        calls += 1
        return original(self, a, b)

    with monkeypatch.context() as patch:
        patch.setattr(owner, "mul", counted_mul)
        ledger = CostLedger(observe_operand_bits=True)
        with ledger.frame(depth=0, wires=2, precision=ring.p,
                          ring_depth=getattr(ring, "depth", 0), schedule="micro"):
            assert _run_packet(native, ring) == expected
    assert calls > 0
    report = ledger.report()
    assert report["frame_tree_reconciled"]
    assert any("/" + owner.__name__ + ".mul/" in k
               for k in report["ring_call_totals"])
    assert report["operand_geometry_totals"]


def test_scoped_flint_keeps_explicit_ring_backend(monkeypatch: pytest.MonkeyPatch) -> None:
    pytest.importorskip("flint")
    native = pytest.importorskip("native_recursive")
    from non_exponential_sudoku.core.flint_backend import flint_arithmetic

    ring = Padic(8, modulus_polynomial(8), 19)
    expected = _run_packet(native, ring)
    original = Padic.mul
    calls = 0

    def counted_mul(self, a, b):
        nonlocal calls
        calls += 1
        return original(self, a, b)

    with monkeypatch.context() as patch:
        patch.setattr(Padic, "mul", counted_mul)
        with flint_arithmetic():
            assert _run_packet(native, ring) == expected
    assert calls > 0


@pytest.mark.parametrize("use_plan", (False, True))
def test_native_leaf_direct_ring_method_bypass_is_exact(
    use_plan: bool, monkeypatch: pytest.MonkeyPatch,
) -> None:
    native = pytest.importorskip("native_recursive")
    ring = Padic(8, modulus_polynomial(8), 17)
    net = simple_network(
        3,
        [((0, 1), {(0, 0): 2, (1, 1): 3}),
         ((2,), {(0,): 4, (1,): 5})],
        [((0, 2), {(0, 1): 2, (1, 0): 6}),
         ((1,), {(0,): 1, (1,): 2})],
    )
    plan = compile_leaf_plan(
        net.edges, tuple(v.ports for v in net.left + net.right),
        max_width=3, lookup_budget=8192,
    ) if use_plan else None
    expected = net.direct(ring, 3)

    def unexpected(*_args, **_kwargs):
        raise AssertionError("eligible native leaf used a Python ring method")

    with monkeypatch.context() as patch:
        patch.setattr(Padic, "add", unexpected)
        patch.setattr(Padic, "mul", unexpected)
        assert native.eliminate_leaf(
            net, ring, 3, max_width=3, plan=plan,
            max_factor_bytes=1 << 20,
        ) == expected
