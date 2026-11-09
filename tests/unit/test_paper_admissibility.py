"""Evidence boundaries: finite inputs cannot masquerade as asymptotic proofs."""
from __future__ import annotations

import pytest

from reference.admissibility import audit_sudoku_root, probe_sudoku_packing
from reference.bit_work import sudoku_direct_encoding_size
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku import ContractionEngine, ContractorConfig
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from non_exponential_sudoku.sudoku.encoding import sudoku_network
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.contraction.engine import paper_schedule_parameters

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize("box_order", (1, 2, 3, 4, 5, 8, 16))
def test_edge_parameterization_satisfies_fixed_C_one(box_order: int) -> None:
    dims = sudoku_direct_encoding_size(box_order)
    audit = audit_sudoku_root(box_order)
    assert audit.s == max(2, dims.wires)
    assert audit.edges <= audit.s
    assert audit.vertices <= 2 * audit.s
    assert audit.precision <= audit.s
    assert audit.degree_hypothesis


def test_vertex_parameterization_ratio_unbounded_on_growing_sudoku_family() -> None:
    # For any k>=1 choose box order b=2**k. Then n=2**(2k),
    # t=2k and M/V = 6kn/(n+3) > 3k. There can be no uniform C.
    for k in (1, 2, 4, 8, 16):
        audit = audit_sudoku_root(1 << k, parameterization="vertices")
        assert audit.edges > 3 * k * audit.s


def test_schedule_activation_requires_lambda_at_least_131072() -> None:
    for lam in (1, 5, 1024, 131071):
        assert paper_schedule_parameters(2 ** (lam - 1) + 1, lam, 0)[2] == 0
    s = (1 << 131071) + 1
    r, a, u, threshold = paper_schedule_parameters(s, 131072, 0)
    assert (r, a, u) == (64, 2, 1)
    assert threshold < s


@pytest.mark.parametrize("box_order", (2, 3, 4))
def test_actual_small_sudoku_root_stops_before_packing(box_order: int) -> None:
    for parameterization in ("edges", "vertices"):
        audit = audit_sudoku_root(box_order, parameterization=parameterization)
        assert audit.branch == "inactive_schedule_leaf"
        assert audit.leaf_capacity_refusal
        assert audit.numerical_preconditions is None


@pytest.mark.parametrize("box_order,expected_packets,expected_modes", (
    (2, 84, 0), (3, 903, 0), (4, 2880, 0),
))
def test_counterfactual_packings_distinguish_assumptions_and_implementation(
    box_order: int, expected_packets: int, expected_modes: int,
) -> None:
    audit = probe_sudoku_packing(box_order)
    assert not audit.root_schedule_active
    assert not audit.paper_numerical_preconditions_met
    assert audit.packet_count == expected_packets
    assert audit.mode_descriptors == expected_modes
    assert audit.real_slots == audit.edges
    assert audit.allocated_slots > 3 * audit.edges
    assert not audit.packet_bound_met  # NOT a counterexample to the lemma's hypotheses.
    assert audit.orientation_geometry_valid and audit.exact_port_conservation
    assert audit.maximum_child_degree > 0
    assert audit.child_vertices > 0
    assert audit.maximum_child_edges <= 2 * audit.edges
    assert not audit.default_mode_budget_exceeded
    # At a=2, i=0, every valid cross coefficient has valuation >=3:
    # no crossing mode survives modulo 2**3 in this forced probe.


def test_counterfactual_9x9_shrinks_children_but_fails_packet_bound() -> None:
    audit = probe_sudoku_packing(3)
    assert audit.child_shrinkage_met
    assert audit.group_load_bound_met
    assert audit.maximum_child_edges == 60
    assert audit.maximum_child_degree == 36
    assert audit.child_vertices == 906


def test_forced_16x16_probe_has_no_nonzero_cross_modes_at_precision_three() -> None:
    # This is a counterfactual geometry probe, not the literal paper path.
    net = sudoku_network(Puzzle(4, (0,) * 256))
    packing = pack(net, 64, 2)
    assert mode_catalog(net, packing, 1, 3, max_modes=2000) == []


def test_input_parameter_and_asymptotic_claim_are_separate() -> None:
    # With b=2**k: N=2**(4k), t=2k, M=6kN. Also the binary
    # logarithm lambda of M is at most 10k for all k>=1.
    # Hence (M/(N*sqrt(lambda)))**2 >= 3.6k, which is unbounded.
    for k in (1, 2, 4, 8, 16, 32):
        audit = audit_sudoku_root(1 << k)
        assert audit.edges == 6 * k * audit.cells
        assert audit.lambda_bits <= 10 * k
        assert (audit.edges // audit.cells) ** 2 >= 36 * k * k


def test_auditor_rejects_unsupported_parameterization() -> None:
    with pytest.raises(ValueError, match="parameterization"):
        audit_sudoku_root(2, parameterization="unknown")  # type: ignore[arg-type]


def test_real_4x4_literal_paper_still_refuses_with_corrected_s() -> None:
    net = sudoku_network(Puzzle(2, (0,) * 16))
    audit = audit_sudoku_root(2)
    assert audit.s == net.edges == 96
    assert audit.precision == 33
    engine = ContractionEngine(ContractorConfig(audit.s, audit.precision, schedule="paper"))
    with pytest.raises(CapacityError, match="Direct leaf has 96 edges; limit is 18"):
        engine.contract(net)
    assert engine.stats.active_paper_calls == 0
