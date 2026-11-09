"""Proof-by-execution contracts for direct packet deformation elimination.

The lifted network sums original Y/X bit variables under packet Cauchy
factors. It never enumerates weighted modes. The independent 2^(2M) oracle
remains the correctness reference for small inputs.
"""
from __future__ import annotations

from dataclasses import replace
from itertools import product
from random import Random

import pytest

from non_exponential_sudoku import (
    ContractionEngine, ContractorConfig, LeafConfig, ModeConfig,
    RecoveryConfig, Padic, simple_network,
)
from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.core.packing import pack
from reference.sudoku_network_oracle import independently_evaluate_F
from non_exponential_sudoku.contraction.packet_factorization import (
    compile_packet_deformation, evaluate_packet_deformation,
)
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.core.jets import JetRing


@pytest.mark.checkpoint
def test_lifted_topology_has_two_ports_per_original_edge() -> None:
    net = simple_network(
        2,
        [((0, 1), {(0, 0): 1, (1, 1): 1})],
        [((0, 1), {(0, 0): 1, (1, 1): 1})],
    )
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    plan = compile_packet_deformation(net, packing, max_width=8)
    assert plan.network.edges == 4
    plan.network.validate()
    assert len(plan.network.right) == len(packing.packets)
    assert all(not hasattr(v.oracle, "modes") for v in plan.network.right)


@pytest.mark.integration
@pytest.mark.parametrize("slots", (2, 4, 8))
@pytest.mark.parametrize("t", (-1, 1))
def test_packet_reordering_matches_independent_deformation(slots: int, t: int) -> None:
    rng = Random(592 + slots + 5*t)
    n = 3
    truth = tuple(product((0, 1), repeat=n))
    left = {row: rng.randrange(3) for row in truth}
    right = {row: rng.randrange(3) for row in truth}
    net = simple_network(n, [((0, 1, 2), left)], [((0, 1, 2), right)])
    a = slots.bit_length() - 1
    packing = pack(net, 2, a, (((0,)*a,), ((1,) + (0,)*(a-1),)))
    engine = ContractionEngine(ContractorConfig(n, 9, schedule="micro"))
    ring = Padic(engine.e, engine.f, 9)
    for z in (ring.zero, ring.scalar(3), ring.basis(2)):
        expected = independently_evaluate_F(net, packing, t, z, ring)
        got = evaluate_packet_deformation(
            net, packing, t, z, ring,
            max_width=12, max_factor_bytes=32*1024*1024,
        )
        assert got == expected


@pytest.mark.integration
def test_nested_jet_value_matches_boolean_oracle() -> None:
    net = simple_network(
        2, [((0, 1), {(0, 0): 1, (1, 1): 1})],
        [((0, 1), {(0, 0): 1, (1, 1): 1})],
    )
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    engine = ContractionEngine(ContractorConfig(2, 7, schedule="micro"))
    base = Padic(engine.e, engine.f, 7)
    ring = JetRing(base, 3)
    got = evaluate_packet_deformation(
        net, packing, 1, ring.variable, ring,
        max_width=8, max_factor_bytes=32*1024*1024,
    )
    expected = independently_evaluate_F(net, packing, 1, ring.variable, ring)
    assert got == expected


@pytest.mark.integration
def test_dense_four_slot_full_recovery_overcomes_mode_factor_refusal() -> None:
    tab = {(0,): 1, (1,): 1}
    net = simple_network(2, [((i,), tab) for i in range(2)],
                         [((i,), tab) for i in range(2)])
    labels = (((0, 0), (0, 0)), ((1, 0), (1, 0)))
    common = dict(
        s=2, precision=5, schedule="geometry64",
        micro_active_depth=1, root_labels=labels,
        recovery=RecoveryConfig(method="jet", streaming=True),
        leaf=LeafConfig(strategy="eliminate", max_width=8,
                        max_factor_bytes=32*1024*1024),
    )
    engine = ContractionEngine(ContractorConfig(
        **common, mode=ModeConfig(strategy="packet_eliminate"),
    ))
    assert engine.contract(net) == engine.contract_complete(net)
    baseline = ContractionEngine(ContractorConfig(
        **common, mode=ModeConfig(strategy="eliminate", native_sparse=False),
    ))
    # At the expanded Hermite precision the original mode factor
    # construction refuses before any child contraction. This is an
    # explicit unsuccessful baseline, not a runtime speedup.
    with pytest.raises(CapacityError, match="factor size limit"):
        baseline.contract(net)
    assert baseline.stats.child_networks == 0
    assert engine.stats.direct_packet_deformations > 0
    assert engine.stats.child_networks == 0


@pytest.mark.checkpoint
def test_packet_elimination_refuses_before_oracle_if_width_too_small() -> None:
    called = [0]
    def oracle(bits, ring):
        called[0] += 1
        return ring.one
    net = Network([Vertex("left", (0, 1, 2), oracle)],
                  [Vertex("right", (0, 1, 2), oracle)], 3)
    packing = pack(net, 2, 2, (((0, 0),), ((1, 0),)))
    with pytest.raises(CapacityError, match="width"):
        compile_packet_deformation(net, packing, max_width=1)
    assert called == [0]


@pytest.mark.checkpoint
def test_mode_strategy_rejects_invalid_value() -> None:
    with pytest.raises(ValueError, match="Invalid mode strategy"):
        ModeConfig(strategy="unknown")


@pytest.mark.integration
def test_twenty_independent_wires_contract_without_exhaustive_bit_cube() -> None:
    # The lifted graph has forty binary wires. Direct 2**40 enumeration
    # would be prohibitive, but all packet/original factors have bounded
    # width and the result follows from independent packet products.
    count = 20
    tab = {(0,): 1, (1,): 1}
    net = simple_network(count, [((i,), tab) for i in range(count)],
                         [((i,), tab) for i in range(count)])
    labels = (tuple((2*i, 0) for i in range(count)),
              tuple((2*i+1, 0) for i in range(count)))
    packing = pack(net, 64, 2, labels)
    engine = ContractionEngine(ContractorConfig(count, count+4,
                                                 schedule="geometry64"))
    ring = Padic(engine.e, engine.f, count+4)
    answer = evaluate_packet_deformation(
        net, packing, 1, ring.zero, ring,
        max_width=8, max_factor_bytes=32*1024*1024,
    )
    assert answer == ring.scalar(1 << count)


@pytest.mark.checkpoint
def test_packet_strategy_does_not_prove_literal_paper_schedule() -> None:
    with pytest.raises(ValueError, match="not the paper recurrence"):
        ContractorConfig(2, 5, mode=ModeConfig(strategy="packet_eliminate"))
