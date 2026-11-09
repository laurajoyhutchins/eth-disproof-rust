"""TDD: prune exact cross-group modes from their proven 2-adic valuations.

The baseline catalog is intentionally independent of the production catalog.
These tests distinguish deleting zero terms from merely optimizing storage.
"""
from __future__ import annotations

from dataclasses import replace
import pytest

from non_exponential_sudoku import ContractionEngine, ContractorConfig, LeafConfig, ModeConfig
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.modes import Mode, mode_catalog, weighted_tuples, cross_mode_valuation
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.contraction.packets import cross_mode_coefficient
from non_exponential_sudoku.sudoku.encoding import port_graph_with_cross_mode, independently_evaluate_F
from non_exponential_sudoku.core.network import simple_network
from reference.legacy_mode_catalog import original_catalog



def case():
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    return net, packing


@pytest.mark.checkpoint
@pytest.mark.parametrize("t", [-1, 1])
@pytest.mark.parametrize("p", [3, 5, 7])
def test_sharpened_mode_catalog_omits_only_provably_zero_modes(t: int, p: int) -> None:
    net, packing = case()
    old = original_catalog(net, packing, t, p)
    got = mode_catalog(net, packing, t, p)
    expected = []
    for mode in old:
        bound = min(
            cross_mode_valuation(t, packing.a, x, mode.y0, mode.b)
            for x in mode.rows
        )
        assert bound >= mode.b + 1
        if bound < p:
            expected.append(replace(mode, weight=bound))
    assert got == expected
    assert len(got) <= len(old)


@pytest.mark.integration
@pytest.mark.parametrize("t", [-1, 1])
def test_cross_coefficient_is_divisible_by_certified_weight(t: int) -> None:
    net, packing = case()
    ring = Padic(5, modulus_polynomial(5), 9)
    old = original_catalog(net, packing, t, ring.p)
    for z in (ring.zero, ring.basis(3), ring.scalar(3)):
        for mode in old:
            for row in mode.rows:
                w = cross_mode_valuation(t, packing.a, row, mode.y0, mode.b)
                value = cross_mode_coefficient(t, z, ring, 1 << packing.a,
                                               row, mode.y0, mode.b)
                assert all(c % (1 << min(w, ring.p)) == 0 for c in value)


@pytest.mark.integration
@pytest.mark.parametrize("t", [-1, 1])
@pytest.mark.parametrize("p", [3, 5])
def test_actual_deformation_matches_unpruned_catalog_and_direct_oracle(
    t: int, p: int,
) -> None:
    net, packing = case()
    old = original_catalog(net, packing, t, p)
    new = mode_catalog(net, packing, t, p)
    assert len(list(weighted_tuples(new, p))) <= len(list(weighted_tuples(old, p)))
    for strategy in ("enumerate", "eliminate"):
        config = ContractorConfig(
            net.edges, p, schedule="micro",
            mode=ModeConfig(strategy=strategy, native_sparse=False),
            leaf=LeafConfig(strategy="eliminate"),
        )
        engine = ContractionEngine(config)
        ring = Padic(engine.e, engine.f, p)
        for z in (ring.zero, ring.basis(3)):
            got = engine.evaluate_deformation(net, packing, new, t, z, ring, 0)
            reference = engine.evaluate_deformation(net, packing, old, t, z, ring, 0)
            direct = independently_evaluate_F(net, packing, t, z, ring)
            assert got == reference == direct


@pytest.mark.integration
def test_valuation_prunes_mode_tuples_even_when_catalog_size_stays_fixed() -> None:
    # Four crossing singleton edges, independent of Sudoku-specific input.
    net = simple_network(
        4,
        [([i], {(0,): 1, (1,): 1}) for i in range(4)],
        [([i], {(0,): 1, (1,): 1}) for i in range(4)],
    )
    labels = (tuple((2*i, 0) for i in range(4)),
              tuple((2*i+1, 0) for i in range(4)))
    packing = pack(net, 64, 2, labels)
    p = 5
    before = original_catalog(net, packing, 1, p)
    after = mode_catalog(net, packing, 1, p)
    assert len(before) == len(after)
    assert all(new.weight >= old.weight for old, new in zip(before, after))
    assert any(new.weight > old.weight for old, new in zip(before, after))
    assert len(list(weighted_tuples(before, p))) > len(list(weighted_tuples(after, p)))
    config = ContractorConfig(
        4, p, schedule="geometry64",
        mode=ModeConfig(strategy="enumerate"),
        leaf=LeafConfig(strategy="eliminate"),
    )
    engine = ContractionEngine(config)
    ring = Padic(engine.e, engine.f, p)
    for z in (ring.zero, ring.basis(3)):
        assert engine.evaluate_deformation(net, packing, before, 1, z, ring, 0) == (
            engine.evaluate_deformation(net, packing, after, 1, z, ring, 0)
        )
