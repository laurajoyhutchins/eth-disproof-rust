"""The canonical direct Sudoku input has a finite, checkable oracle ABI.

The direct-network evaluator remains an independent semantic oracle. Arbitrary
Python callables and perturbed input topology must fail certification.
"""
from __future__ import annotations

from itertools import product
from random import Random

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.sudoku.direct_network import DirectNetwork
from non_exponential_sudoku.sudoku.encoding import sudoku_network
from non_exponential_sudoku.sudoku.input_oracles import CellEntryOracle, UnitEntryOracle
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.sudoku_oracle_cost import (
    UncertifiedSudokuInput,
    certify_original_sudoku_oracles,
    original_oracle_bit_work_per_pass,
)

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize("box_order", [1, 2, 3, 4])
def test_certified_sudoku_input_has_exact_source_arity_and_count(box_order: int) -> None:
    side = box_order * box_order
    puzzle = Puzzle(box_order, (0,) * (side * side))
    graph = sudoku_network(puzzle)
    proof = certify_original_sudoku_oracles(puzzle, graph)
    t = max(1, (side - 1).bit_length())
    assert proof.cells == side * side
    assert proof.units == 3 * side
    assert proof.vertices == side * side + 3 * side
    assert proof.wires == 3 * side * side * t
    assert proof.cell_work.validated_bits == proof.cell_work.decoded_bits == 3 * t
    assert proof.unit_work.validated_bits == proof.unit_work.decoded_bits == side * t
    assert proof.unit_work.distinctness_mask_bits == 1 << t
    assert proof.cell_work.ring_scalar_calls == proof.unit_work.ring_scalar_calls == 1
    assert proof.per_pass_boolean_bit_work_ceiling > 0
    assert proof.per_pass_scalar_calls == proof.vertices
    assert proof.per_pass_boolean_bit_work_ceiling >= (
        proof.cells * proof.cell_work.boolean_bit_work_ceiling +
        proof.units * proof.unit_work.boolean_bit_work_ceiling
    )
    envelope = original_oracle_bit_work_per_pass(proof, extension_degree=5, precision=13)
    assert envelope > proof.per_pass_boolean_bit_work_ceiling


def _same_oracle_as_direct(puzzle: Puzzle, vertex_index: int,
                           bit_assignments: list[tuple[int, ...]]) -> None:
    original = DirectNetwork.from_puzzle(puzzle)
    net = sudoku_network(puzzle)
    ring = Padic(3, modulus_polynomial(3), 7)
    old = original.vertices[vertex_index]
    new = (net.left + net.right)[vertex_index]
    assert new.name == old.name and new.ports == old.ports
    for bits in bit_assignments:
        assignment = [0] * original.edge_count
        for edge, bit in zip(old.ports, bits):
            assignment[edge] = bit
        expected = original.local_entry(old, assignment)
        assert new.oracle(bits, ring) == ring.scalar(expected)


def test_exhaustive_four_by_four_cell_and_unit_entry_equivalence() -> None:
    p = Puzzle(2, (0,) * 16)
    net = sudoku_network(p)
    assert all(type(v.oracle) is CellEntryOracle for v in net.left)
    assert all(type(v.oracle) is UnitEntryOracle for v in net.right)
    for vertex_index in (0, 1, 15, 16, 17, 27):
        arity = len((net.left + net.right)[vertex_index].ports)
        bits = list(product((0, 1), repeat=arity))
        _same_oracle_as_direct(p, vertex_index, bits)


def test_clues_and_large_unit_values_match_independent_direct_reference() -> None:
    rng = Random(1109)
    for box_order in (2, 3, 4):
        side = box_order**2
        entries = tuple(rng.randrange(side + 1) for _ in range(side * side))
        p = Puzzle(box_order, entries)
        graph = sudoku_network(p)
        for vertex_index in (0, side * side // 2, side * side - 1,
                             side * side, side * side + side, len(graph.left) + len(graph.right) - 1):
            arity = len((graph.left + graph.right)[vertex_index].ports)
            bits = [tuple(rng.getrandbits(1) for _ in range(arity)) for _ in range(15)]
            _same_oracle_as_direct(p, vertex_index, bits)

    # 9x9 has four bits per digit, so the independent unit reference allows
    # values >=9 locally. The cell factors (not unit factors) reject them.
    p = Puzzle(3, (0,) * 81)
    unit = sudoku_network(p).right[0].oracle
    digits = list(range(8)) + [15]
    bits = tuple((digit >> bit) & 1 for digit in digits for bit in range(4))
    ring = Padic(3, modulus_polynomial(3), 7)
    assert unit(bits, ring) == ring.one


def test_public_input_oracles_reject_nonboolean_or_wrong_length() -> None:
    ring = Padic(3, modulus_polynomial(3), 7)
    for oracle, count in ((CellEntryOracle(9, 4, 0), 12),
                          (UnitEntryOracle(9, 4), 36)):
        with pytest.raises(ValueError, match="Non-Boolean port"):
            oracle((0,) * (count - 1), ring)
        with pytest.raises(ValueError, match="Non-Boolean port"):
            oracle((2,) + (0,) * (count - 1), ring)


def test_auditor_rejects_unknown_callback_and_changed_input() -> None:
    puzzle = Puzzle(2, (0,) * 16)
    graph = sudoku_network(puzzle)
    valid = certify_original_sudoku_oracles(puzzle, graph)
    assert valid.vertices == 28
    bogus = Network(
        [Vertex(v.name, v.ports, (lambda bits, R: R.one)) if i == 0 else v
         for i, v in enumerate(graph.left)], list(graph.right), graph.edges
    )
    with pytest.raises(UncertifiedSudokuInput, match="canonical"):
        certify_original_sudoku_oracles(puzzle, bogus)
    changed = Puzzle(2, (1,) + (0,) * 15)
    with pytest.raises(UncertifiedSudokuInput, match="clue"):
        certify_original_sudoku_oracles(changed, graph)
    other = Network(list(graph.left), list(graph.right), graph.edges)
    other.right[0] = Vertex("row:changed", other.right[0].ports, other.right[0].oracle)
    with pytest.raises(UncertifiedSudokuInput, match="name"):
        certify_original_sudoku_oracles(puzzle, other)
    swapped = Network(list(graph.left), list(graph.right), graph.edges)
    one, two = swapped.right[:2]
    swapped.right[:2] = [two, one]
    with pytest.raises(UncertifiedSudokuInput, match="ports|name"):
        certify_original_sudoku_oracles(puzzle, swapped)
    for e, p in ((1, 0), (0, 7), (4, 0)):
        with pytest.raises(ValueError):
            original_oracle_bit_work_per_pass(valid, extension_degree=e, precision=p)


def test_original_oracle_ring_scalar_returns_exact_canonical_value() -> None:
    class ScalarSpy:
        def __init__(self, ring: Padic) -> None:
            self.ring = ring
            self.calls: list[int] = []

        def scalar(self, value: int) -> tuple[int, ...]:
            self.calls.append(value)
            return self.ring.scalar(value)

    p = Puzzle(2, (0,) * 16)
    net = sudoku_network(p)
    ring = Padic(3, modulus_polynomial(3), 7)
    for vertex in net.left[:2] + net.right[:2]:
        spy = ScalarSpy(ring)
        bits = tuple(0 for _ in vertex.ports)
        result = vertex.oracle(bits, spy)  # type: ignore[arg-type]
        assert spy.calls in ([0], [1])
        assert result == ring.scalar(spy.calls[0])


@pytest.mark.parametrize("box_order", [2, 3, 4])
def test_conditional_frame_model_can_validate_original_sudoku_oracles(
    box_order: int,
) -> None:
    from non_exponential_sudoku.runtime.config import ContractorConfig, ModeConfig
    from reference.whole_frame_recurrence import (
        UnclosedRecurrence, assemble_paper_recurrence,
    )

    side = box_order**2
    puzzle = Puzzle(box_order, (0,) * (side * side))
    net = sudoku_network(puzzle)
    certificate = certify_original_sudoku_oracles(puzzle, net)
    precision = certificate.cells * certificate.digit_width + 1
    cfg = ContractorConfig(
        s=net.edges, precision=precision, schedule="paper",
        mode=ModeConfig(native_sparse=False),
    )
    model = assemble_paper_recurrence(
        cfg, edges=net.edges, vertices=certificate.vertices,
        input_name_bits=certificate.root_name_bits,
        original_sudoku=(puzzle, net),
    )
    assert model.sudoku_original_oracle_scalar_calls_per_pass == certificate.vertices
    assert model.sudoku_original_oracle_per_pass_bit_work is not None
    assert model.sudoku_original_oracle_per_pass_bit_work >= (
        certificate.per_pass_boolean_bit_work_ceiling
    )
    assert "input_oracle_bit_contract_and_uniform_metadata" in model.open_premises
    with pytest.raises(UnclosedRecurrence, match="unproved"):
        model.require_complete_theorem()
    no_certificate = assemble_paper_recurrence(
        cfg, edges=net.edges, vertices=certificate.vertices,
        input_name_bits=certificate.root_name_bits,
    )
    assert no_certificate.sudoku_original_oracle_per_pass_bit_work is None
    with pytest.raises(UnclosedRecurrence, match="metadata mismatch"):
        assemble_paper_recurrence(
            cfg, edges=net.edges, vertices=certificate.vertices,
            input_name_bits=certificate.root_name_bits - 1,
            original_sudoku=(puzzle, net),
        )
    with pytest.raises(UnclosedRecurrence, match="precision insufficient"):
        assemble_paper_recurrence(
            ContractorConfig(
                s=net.edges, precision=precision - 1, schedule="paper",
                mode=ModeConfig(native_sparse=False),
            ),
            edges=net.edges, vertices=certificate.vertices,
            input_name_bits=certificate.root_name_bits,
            original_sudoku=(puzzle, net),
        )


def test_conditional_model_rejects_forged_original_oracle_type() -> None:
    from non_exponential_sudoku.runtime.config import ContractorConfig, ModeConfig
    from reference.whole_frame_recurrence import (
        UnclosedRecurrence, assemble_paper_recurrence,
    )

    puzzle = Puzzle(2, (0,) * 16)
    net = sudoku_network(puzzle)
    proof = certify_original_sudoku_oracles(puzzle, net)
    bad = Network(
        [Vertex(v.name, v.ports, lambda bits, ring: ring.one) if j == 0 else v
         for j, v in enumerate(net.left)],
        list(net.right), net.edges,
    )
    cfg = ContractorConfig(s=net.edges, precision=proof.cells * proof.digit_width + 1,
                           schedule="paper", mode=ModeConfig(native_sparse=False))
    with pytest.raises(UnclosedRecurrence, match="uncertified"):
        assemble_paper_recurrence(
            cfg, edges=net.edges, vertices=proof.vertices,
            input_name_bits=proof.root_name_bits, original_sudoku=(puzzle, bad),
        )
