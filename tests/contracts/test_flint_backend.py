"""FLINT's optional production path must preserve ring and solver semantics."""
from __future__ import annotations

import random

import pytest

import non_exponential_sudoku.core.algebra as algebra
from non_exponential_sudoku import (
    ContractionEngine, ContractorConfig, LeafConfig, ModeConfig, simple_network,
)
from non_exponential_sudoku.core.flint_backend import flint_arithmetic, flint_enabled
from non_exponential_sudoku.runtime.cost_ledger import CostLedger

pytestmark = pytest.mark.checkpoint


def test_default_is_native_or_python_and_never_flint() -> None:
    assert not flint_enabled()
    ring = algebra.Padic(3, algebra.modulus_polynomial(3), 8)
    assert ring.mul(ring.one, ring.one) == ring.one
    assert not flint_enabled()


def test_missing_flint_is_not_a_silent_fallback(monkeypatch: pytest.MonkeyPatch) -> None:
    import non_exponential_sudoku.core.flint_backend as backend
    original_import = backend.importlib.import_module

    def reject_flint(name: str) -> object:
        if name == "flint":
            raise ImportError("simulated missing optional dependency")
        return original_import(name)

    monkeypatch.setattr(backend.importlib, "import_module", reject_flint)
    with pytest.raises(RuntimeError, match="optional python-flint"):
        with flint_arithmetic():
            pytest.fail("context must refuse before executing its body")
    assert not flint_enabled()


@pytest.mark.requires_flint
@pytest.mark.parametrize("degree,precision", [
    (3, 8), (5, 64), (8, 256), (16, 256), (32, 1024), (64, 256),
])
def test_opt_in_flint_matches_python_and_native(
    degree: int, precision: int, monkeypatch: pytest.MonkeyPatch,
) -> None:
    pytest.importorskip("flint")
    ring = algebra.Padic(degree, algebra.modulus_polynomial(degree), precision)
    randomizer = random.Random(degree * 3001 + precision)
    modulus = 1 << precision
    pairs = [
        (
            tuple(randomizer.randrange(-modulus, 2 * modulus) for _ in range(degree)),
            tuple(randomizer.randrange(-modulus, 2 * modulus) for _ in range(degree)),
        ) for _ in range(8)
    ] + [(ring.zero, ring.one), (ring.one, ring.one)]
    monkeypatch.setattr(algebra, "_native_ring", None)
    expected = [ring.mul(a, b) for a, b in pairs]
    assert not flint_enabled()
    with flint_arithmetic():
        assert flint_enabled()
        observed = [ring.mul(a, b) for a, b in pairs]
        with flint_arithmetic():
            assert ring.mul(ring.one, ring.one) == ring.one
        assert flint_enabled()
        assert ring.pow(ring.basis(3), 3) == ring.mul(ring.mul(ring.basis(3), ring.basis(3)), ring.basis(3))
    assert not flint_enabled()
    assert observed == expected


@pytest.mark.requires_flint
def test_2adic_unit_and_nonunit_semantics() -> None:
    pytest.importorskip("flint")
    ring = algebra.Padic(5, algebra.modulus_polynomial(5), 64)
    with flint_arithmetic():
        inverse = ring.inv(ring.basis(7))
        assert ring.mul(ring.basis(7), inverse) == ring.one
        with pytest.raises(ZeroDivisionError):
            ring.inv(ring.scalar(2))
    assert not flint_enabled()


@pytest.mark.requires_flint
def test_ledger_attributes_flint_native_boundary() -> None:
    pytest.importorskip("flint")
    ring = algebra.Padic(3, algebra.modulus_polynomial(3), 8)
    ledger = CostLedger()
    with ledger.frame(depth=0, wires=1, precision=8, ring_depth=0, schedule="micro"):
        with flint_arithmetic():
            assert ring.mul(ring.one, ring.one) == ring.one
    report = ledger.report()
    assert report["opaque_native_calls"] == {"flint_padic_mul": 1}
    assert report["frame_tree_reconciled"] is True


@pytest.mark.requires_flint
def test_complete_small_contraction_matches_default() -> None:
    pytest.importorskip("flint")
    network = simple_network(2,
        [([0], {(0,): 1, (1,): 1}), ([1], {(0,): 1, (1,): 1})],
        [([0], {(0,): 1, (1,): 1}), ([1], {(0,): 1, (1,): 1})],
    )
    config = ContractorConfig(
        s=2, precision=6, schedule="micro",
        mode=ModeConfig(strategy="eliminate", factorization="components"),
        leaf=LeafConfig(strategy="eliminate"),
    )
    expected = ContractionEngine(config).contract(network)
    with flint_arithmetic():
        actual = ContractionEngine(config).contract(network)
    assert actual == expected
    assert actual[0] == 4
