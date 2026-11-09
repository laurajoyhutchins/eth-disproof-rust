"""Falsifiable checks for the *interface* to the paper contraction theorem.

This is a research auditor, not a solver admission certificate. The finite
packet probes deliberately do NOT claim that an inactive paper schedule
executed a recursive step or that the large-size packing lemma failed.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Literal

from non_exponential_sudoku.contraction.children import child_edge_audit, ceil_ninth_tenths, make_child
from non_exponential_sudoku.contraction.engine import paper_schedule_parameters
from non_exponential_sudoku.contraction.packets import EvaluationContext
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.packing import audit_packing, pack
from non_exponential_sudoku.sudoku.encoding import sudoku_network
from non_exponential_sudoku.sudoku.three_cnf import Puzzle

from .bit_work import sudoku_direct_encoding_size


@dataclass(frozen=True)
class RootAudit:
    box_order: int
    side: int
    cells: int
    edges: int
    vertices: int
    precision: int
    s: int
    parameterization: Literal["edges", "vertices"]
    max_degree: int
    degree_ceiling: int
    edge_to_s_ratio_numerator: int
    edge_to_s_ratio_denominator: int
    lambda_bits: int
    groups: int
    slot_exponent: int
    active_coordinates: int
    leaf_threshold: int
    branch: Literal[
        "inactive_schedule_leaf", "small_network_leaf",
        "numerical_preconditions_leaf", "eligible_to_attempt_packing",
        "degree_hypothesis_violation",
    ]
    degree_hypothesis: bool
    input_precision_hypothesis: bool
    numerical_preconditions: bool | None
    leaf_capacity_refusal: bool

    def as_record(self) -> dict[str, object]:
        return asdict(self)


def audit_sudoku_root(box_order: int, *, parameterization: Literal["edges", "vertices"] = "edges",
                      leaf_limit: int = 18) -> RootAudit:
    """Check finite root numerical hypotheses; no tensor network allocated.

    The paper's M<=Cs requires *one* C over the growing family, not a
    C chosen separately for each row. For the direct reduction s=M gives
    C=1, while s=V gives an unbounded M/s ratio.
    """
    if parameterization not in ("edges", "vertices"):
        raise ValueError("parameterization must be edges or vertices")
    if leaf_limit < 1:
        raise ValueError("leaf_limit must be positive")
    dims = sudoku_direct_encoding_size(box_order)
    s = max(2, dims.wires if parameterization == "edges" else dims.vertices)
    lam = max(1, (s - 1).bit_length())
    r, a, u, threshold = paper_schedule_parameters(s, lam, 0)
    delta = ceil_ninth_tenths(s)
    degree_ok = dims.maximum_degree <= delta
    numerical: bool | None = None
    if not u:
        branch = "inactive_schedule_leaf"
    elif dims.wires <= threshold:
        branch = "small_network_leaf"
    else:
        L = 1 << a
        Darr = r ** (2 * a)
        numerical = (dims.wires >= 2 * Darr * Darr * delta
                     and dims.wires >= L * Darr and 2 * L <= delta)
        if not degree_ok:
            # Production checks maximum degree before the numerical gates.
            branch = "degree_hypothesis_violation"
        else:
            branch = ("eligible_to_attempt_packing" if numerical
                      else "numerical_preconditions_leaf")
    return RootAudit(
        box_order, dims.side, dims.cells, dims.wires, dims.vertices,
        dims.sufficient_count_precision, s, parameterization,
        dims.maximum_degree, delta, dims.wires, s,
        lam, r, a, u, threshold, branch, degree_ok,
        dims.sufficient_count_precision <= s, numerical,
        branch in ("inactive_schedule_leaf", "small_network_leaf",
                   "numerical_preconditions_leaf") and dims.wires > leaf_limit,
    )


@dataclass(frozen=True)
class CounterfactualPackingProbe:
    box_order: int
    slot_exponent: int
    root_schedule_active: bool
    paper_numerical_preconditions_met: bool
    edges: int
    packet_count: int
    real_slots: int
    allocated_slots: int
    packet_bound_met: bool
    group_load_bound_met: bool
    orientation_geometry_valid: bool
    exact_port_conservation: bool
    child_shrinkage_met: bool
    maximum_child_edges: int
    maximum_child_degree: int
    child_vertices: int
    mode_descriptors: int
    default_mode_budget_exceeded: bool

    def as_record(self) -> dict[str, object]:
        return asdict(self)


def probe_sudoku_packing(box_order: int, *, slot_exponent: int = 2,
                         mode_precision: int = 3, default_mode_budget: int = 2000,
                         materialize_child: bool = True) -> CounterfactualPackingProbe:
    """Probe a *counterfactual* r=64 packing even if the schedule is inactive.

    Actual child construction uses the maximum-load group, t=1, and an
    all-zero mode multiplicity at a deliberately tiny precision. The child
    graph topology is independent of those multiplicities; the coefficient
    oracles are NOT used as a proof of recursive evaluation cost.
    """
    if slot_exponent < 1 or mode_precision < 1 or default_mode_budget < 1:
        raise ValueError("positive audit parameters required")
    if slot_exponent > 10:
        raise ValueError("counterfactual geometry probe is bounded to a<=10")
    dims = sudoku_direct_encoding_size(box_order)
    net = sudoku_network(Puzzle(box_order, (0,) * dims.cells))
    packing = pack(net, 64, slot_exponent)
    audit = audit_packing(net, packing)
    edge_audits = [child_edge_audit(net, packing, i) for i in range(slot_exponent)]
    all_loads = edge_audits[0]["edges_by_group"]
    group = max(range(64), key=lambda g: all_loads[g])
    modes = mode_catalog(net, packing, 1, mode_precision, max_modes=10_000_000)
    if materialize_child:
        ring = Padic(5, modulus_polynomial(5), mode_precision)
        context = EvaluationContext(1, ring.one, ring, packing.a)
        child = make_child(net, packing, modes, (0,) * len(modes),
                           1, ring.one, ring, group, 0, context)
        child.validate()
        if child.edges != all_loads[group]:
            raise AssertionError("constructed child's edge count differs from independent load count")
        child_degree = max((len(v.ports) for v in child.left + child.right), default=0)
        child_vertices = len(child.left) + len(child.right)
        if child_vertices > dims.vertices + dims.wires:
            raise AssertionError("child vertex envelope violated")
    else:
        child_degree = -1
        child_vertices = -1
    root = audit_sudoku_root(box_order)
    # The paper's numerical hypotheses must be checked for *this* forced
    # a, not inferred from the inactive literal schedule (which has a=0).
    L = 1 << slot_exponent
    Darr = 64 ** (2 * slot_exponent)
    numerical = (dims.wires >= 2 * Darr * Darr * root.degree_ceiling
                 and dims.wires >= L * Darr and 2 * L <= root.degree_ceiling)
    return CounterfactualPackingProbe(
        box_order, slot_exponent, root.active_coordinates > 0,
        numerical, dims.wires,
        audit["packet_count"], dims.wires, audit["packet_count"] * (1 << slot_exponent),
        audit["packet_bound_met"], audit["group_load_bound_met"],
        audit["orientation_geometry_valid"],
        all(c["exact_port_conservation"] for c in edge_audits),
        all(c["paper_shrinkage_satisfied"] for c in edge_audits),
        max(c["max_child_edges"] for c in edge_audits),
        child_degree, child_vertices, len(modes),
        len(modes) > default_mode_budget,
    )
