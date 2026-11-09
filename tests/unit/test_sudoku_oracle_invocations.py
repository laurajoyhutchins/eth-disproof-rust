"""TDD for source-proven original Sudoku oracle *invocation* ceilings.

Event counts are separate from arithmetic-bit costs. All direct and factor
rows are tested against the actual engine, including uncompiled fallback
and zero-support. The whole-tree bound remains CONDITIONAL on the paper
fanout bound and source-preserving oracle inheritance.
"""
from __future__ import annotations

from itertools import product

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.network import (
    Network, Vertex, compile_leaf_plan, eliminate_leaf,
)
from non_exponential_sudoku.contraction.zero_support import certify_zero
from non_exponential_sudoku.runtime.config import (
    ContractorConfig, ModeConfig, ZeroSupportPolicy,
)
from non_exponential_sudoku.sudoku.encoding import sudoku_network
from non_exponential_sudoku.sudoku.input_oracles import (
    CellEntryOracle, UnitEntryOracle,
)
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.sudoku_oracle_cost import certify_original_sudoku_oracles
from reference.sudoku_oracle_invocations import (
    UncertifiedOriginalOracleCalls, original_oracle_invocation_envelope,
    audit_retained_original_oracles,
)
from reference.whole_frame_recurrence import (
    UnclosedRecurrence, assemble_paper_recurrence,
)

pytestmark = pytest.mark.checkpoint


def _track(monkeypatch: pytest.MonkeyPatch) -> dict[str, int]:
    calls = {"cell": 0, "unit": 0}
    old_cell = CellEntryOracle.__call__
    old_unit = UnitEntryOracle.__call__

    def cell(self: CellEntryOracle, bits: tuple[int, ...], ring: object) -> object:
        calls["cell"] += 1
        return old_cell(self, bits, ring)  # type: ignore[arg-type]

    def unit(self: UnitEntryOracle, bits: tuple[int, ...], ring: object) -> object:
        calls["unit"] += 1
        return old_unit(self, bits, ring)  # type: ignore[arg-type]

    monkeypatch.setattr(CellEntryOracle, "__call__", cell)
    monkeypatch.setattr(UnitEntryOracle, "__call__", unit)
    return calls


def _root(b: int = 1) -> tuple[Puzzle, Network]:
    side = b * b
    puzzle = Puzzle(b, (0,) * (side * side))
    return puzzle, sudoku_network(puzzle)


def test_symbolic_density_exposes_avoided_exponential_table_size() -> None:
    for b in (1, 2, 3, 4):
        puzzle, net = _root(b)
        proof = certify_original_sudoku_oracles(puzzle, net)
        bound = original_oracle_invocation_envelope(proof)
        t = proof.digit_width
        assert bound.dense_factor_calls == (
            proof.cells * (1 << (3 * t)) +
            proof.units * (1 << (proof.side * t))
        )
        assert bound.max_unit_arity == proof.side * t
        assert bound.max_cell_arity == 3 * t
        assert bound.dense_factor_calls_log2_ceiling >= (
            bound.dense_factor_calls - 1
        ).bit_length()
        assert bound.direct_per_node_log2_ceiling == (
            proof.wires + (proof.vertices - 1).bit_length()
        )
        assert bound.support_check_per_node_log2_ceiling == 0
        assert bound.per_potential_node_log2_ceiling >= (
            bound.dense_factor_calls_log2_ceiling
        )
        assert bound.all_potential_nodes_log2_ceiling is None
        assert not bound.proves_subexponential_totality
    # Dense tables are already impractical even with few clue changes.
    assert original_oracle_invocation_envelope(
        certify_original_sudoku_oracles(*_root(3))
    ).max_unit_arity == 36
    assert original_oracle_invocation_envelope(
        certify_original_sudoku_oracles(*_root(4))
    ).max_unit_arity == 64


def test_python_direct_and_compiled_factor_table_counts(monkeypatch: pytest.MonkeyPatch) -> None:
    puzzle, net = _root(1)
    bound = original_oracle_invocation_envelope(
        certify_original_sudoku_oracles(puzzle, net)
    )
    ring = Padic(3, modulus_polynomial(3), 8)
    calls = _track(monkeypatch)
    expected = net.direct(ring, net.edges)
    assert expected == ring.one
    assert calls["cell"] + calls["unit"] <= (
        1 << bound.direct_per_node_log2_ceiling
    )
    calls.update(cell=0, unit=0)

    assert eliminate_leaf(net, ring, net.edges, max_width=4) == expected
    assert calls == {"cell": 1 << 3, "unit": 3 * (1 << 1)}
    assert sum(calls.values()) == bound.dense_factor_calls
    calls.update(cell=0, unit=0)

    scopes = tuple(v.ports for v in net.left + net.right if v.ports)
    plan = compile_leaf_plan(net.edges, scopes, max_width=4)
    assert plan is not None
    assert eliminate_leaf(net, ring, net.edges, max_width=4, plan=plan) == expected
    assert sum(calls.values()) == bound.dense_factor_calls


def test_optional_zero_support_uses_at_most_one_additional_table_pass(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    puzzle, net = _root(1)
    proof = certify_original_sudoku_oracles(puzzle, net)
    bound = original_oracle_invocation_envelope(proof, zero_support=True)
    assert bound.support_check_per_node_log2_ceiling > 0
    ring = Padic(3, modulus_polynomial(3), 8)
    calls = _track(monkeypatch)
    policy = ZeroSupportPolicy(enabled=True, max_child_edges=8,
                               max_vertex_arity=8, max_support_rows=100)
    result = certify_zero(net, ring, policy)
    assert result.verdict in ("zero", "possible")
    assert sum(calls.values()) <= proof.cells * (1 << 3) + proof.units * (1 << 1)
    assert result.evaluated_rows <= bound.dense_factor_calls
    policy = ZeroSupportPolicy(enabled=True, max_child_edges=1,
                               max_vertex_arity=8, max_support_rows=100)
    calls.update(cell=0, unit=0)
    assert certify_zero(net, ring, policy).verdict == "unsupported"
    assert sum(calls.values()) == 0


def test_uncompiled_elimination_fallback_charges_both_table_and_direct(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    puzzle, root = _root(1)
    proof = certify_original_sudoku_oracles(puzzle, root)
    ring = Padic(3, modulus_polynomial(3), 8)
    unit = root.right[0].oracle
    cell = root.left[0].oracle
    # A standalone factor-schedule regression: first factor has arity one,
    # second arity three exceeds max_width=2, so direct() is called after
    # the first factor has already been materialized.
    net = Network(
        [Vertex("first", (0,), unit),
         Vertex("second", (1, 2, 3), cell)],
        [Vertex(f"R{i}", (i,), lambda bits, R: R.one) for i in range(4)],
        4,
    )
    net.validate()
    calls = _track(monkeypatch)
    result = eliminate_leaf(net, ring, 4, max_width=2)
    assert result == net.direct(ring, 4)
    # There are at most 2^4 full assignments; each original oracle is
    # present once, plus up to two pre-materialized first-factor entries.
    assert calls["unit"] <= 2 + 2 * (1 << 4)
    assert calls["cell"] <= 2 * (1 << 4)
    assert sum(calls.values()) <= 2 + 4 * (1 << 4)
    assert original_oracle_invocation_envelope(
        proof, max_leaf_edges=4,
    ).per_potential_node_log2_ceiling >= (sum(calls.values()) - 1).bit_length()


def test_retained_original_callbacks_must_be_identical_and_keep_arity() -> None:
    puzzle, root = _root(1)
    proof = certify_original_sudoku_oracles(puzzle, root)
    assert audit_retained_original_oracles(puzzle, root, root) == proof.vertices
    altered = Network(
        [Vertex("bad", (0, 1), root.left[0].oracle)],
        [Vertex("dummy0", (0,), root.right[0].oracle),
         Vertex("dummy1", (1,), root.right[1].oracle)],
        2,
    )
    altered.validate()
    with pytest.raises(UncertifiedOriginalOracleCalls, match="arity"):
        audit_retained_original_oracles(puzzle, root, altered)
    foreign = Network(
        [Vertex("bad", (0,), UnitEntryOracle(1, 1))],
        [Vertex("dummy0", (0,), root.right[0].oracle)],
        1,
    )
    foreign.validate()
    with pytest.raises(UncertifiedOriginalOracleCalls, match="identity"):
        audit_retained_original_oracles(puzzle, root, foreign)


def test_conditional_whole_tree_event_bound_does_not_close_paper_theorem() -> None:
    puzzle, net = _root(2)
    proof = certify_original_sudoku_oracles(puzzle, net)
    cfg = ContractorConfig(
        s=net.edges, precision=proof.cells * proof.digit_width + 1,
        schedule="paper", mode=ModeConfig(native_sparse=False),
    )
    model = assemble_paper_recurrence(
        cfg, edges=net.edges, vertices=proof.vertices,
        input_name_bits=proof.root_name_bits,
        original_sudoku=(puzzle, net),
    )
    calls = model.sudoku_original_oracle_invocation_envelope
    assert calls is not None
    assert calls.per_potential_node_log2_ceiling > 0
    assert calls.all_potential_nodes_log2_ceiling is not None
    assert calls.all_potential_nodes_log2_ceiling >= (
        calls.per_potential_node_log2_ceiling
    )
    assert calls.max_leaf_edges == net.edges
    assert calls.all_potential_nodes_bit_work_log2_ceiling is not None
    assert "early_numeric_fallback_covered_by_terminal_cost" in model.open_premises
    assert "resource_limits_do_not_refuse_valid_inputs" in model.open_premises
    with pytest.raises(UnclosedRecurrence):
        model.require_complete_theorem()


def test_invalid_analytic_assumptions_fail_closed() -> None:
    proof = certify_original_sudoku_oracles(*_root(1))
    for val in (-1, True, 2.4):
        with pytest.raises(ValueError):
            original_oracle_invocation_envelope(
                proof, max_leaf_edges=val,  # type: ignore[arg-type]
            )
        with pytest.raises(ValueError):
            original_oracle_invocation_envelope(
                proof, potential_nodes_log2_ceiling=val,  # type: ignore[arg-type]
            )
    with pytest.raises(ValueError):
        original_oracle_invocation_envelope(
            proof, leaf_strategy="unknown",  # type: ignore[arg-type]
        )
