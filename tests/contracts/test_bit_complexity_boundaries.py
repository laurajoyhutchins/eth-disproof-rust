"""Executable witnesses for the finite bit-complexity research boundary."""
from __future__ import annotations

import pytest

from non_exponential_sudoku import ContractionEngine, ContractorConfig
from non_exponential_sudoku.core.algebra import Padic, interpolate, interp_points, modulus_polynomial, p_eval
from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.sudoku.encoding import sudoku_network
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.bit_work import direct_leaf_work, interpolation_work, sudoku_direct_encoding_size
from reference.precision_envelope import (
    max_padic_vector_bits, paper_frame_envelopes, recursive_call_bound_from_frames,
)
from reference.recurrence_calls import recursive_call_bound

pytestmark = pytest.mark.checkpoint


def test_actual_blank_4x4_sudoku_refuses_literal_paper_leaf() -> None:
    """A real Sudoku input proves the current default is not total."""
    puzzle = Puzzle(2, (0,) * 16)
    network = sudoku_network(puzzle)
    assert network.edges == 96
    assert len(network.left) + len(network.right) == 28
    config = ContractorConfig(s=28, precision=sudoku_direct_encoding_size(2).sufficient_count_precision, schedule="paper")
    engine = ContractionEngine(config)
    _, _, u, _ = engine.params(0, network.edges)
    assert u == 0
    with pytest.raises(CapacityError, match="Direct leaf has 96 edges; limit is 18"):
        engine.contract(network)
    assert engine.stats.recursive_calls == 1


@pytest.mark.parametrize("wires,isolated", [(0, 3), (1, 2), (2, 1), (3, 0)])
def test_direct_leaf_event_upper_bound_attained(wires: int, isolated: int) -> None:
    """Constant-one oracles attain the oracle and multiplication upper counts."""
    R = Padic(3, modulus_polynomial(3), 8)
    calls = [0]

    def oracle(bits: tuple[int, ...], ring: Padic) -> tuple[int, ...]:
        calls[0] += 1
        return ring.one

    left = [Vertex(f"l{i}", (i,), oracle) for i in range(wires)]
    right = [Vertex(f"r{i}", (i,), oracle) for i in range(wires)]
    left.extend(Vertex(f"isolated{i}", (), oracle) for i in range(isolated))
    network = Network(left, right, wires)
    network.validate()
    envelope = direct_leaf_work(wires, len(left) + len(right))
    assert network.direct(R, wires) == R.scalar(1 << wires)
    assert calls[0] == envelope.vertex_oracle_calls
    assert envelope.coefficient_multiplications == envelope.vertex_oracle_calls
    assert envelope.coefficient_additions == envelope.edge_assignments
    assert envelope.assignment_bit_reads == (2 * wires) * (1 << wires)


def test_zero_edge_family_requires_unbounded_oracle_calls() -> None:
    """M=0 is fixed; vertex count is a necessary separate size parameter."""
    R = Padic(3, modulus_polynomial(3), 4)
    for vertices in (1, 8, 64):
        calls = [0]

        def oracle(bits: tuple[int, ...], ring: Padic) -> tuple[int, ...]:
            calls[0] += 1
            return ring.one

        network = Network([Vertex(str(i), (), oracle) for i in range(vertices)], [], 0)
        network.validate()
        assert network.direct(R, 0) == R.one
        assert calls[0] == vertices
        assert direct_leaf_work(0, vertices).vertex_oracle_calls == vertices


def test_interpolation_envelope_covers_actual_ring_calls() -> None:
    """Count outer arithmetic calls without charging inner Padic.inv twice."""
    base = Padic(4, modulus_polynomial(4), 7)

    class CountingRing:
        def __init__(self) -> None:
            self.zero = base.zero
            self.one = base.one
            self.multiplications = 0
            self.additions = 0
            self.inversions = 0

        def mul(self, a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
            self.multiplications += 1
            return base.mul(a, b)

        def add(self, a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
            self.additions += 1
            return base.add(a, b)

        def sub(self, a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
            self.additions += 1
            return base.sub(a, b)

        def neg(self, a: tuple[int, ...]) -> tuple[int, ...]:
            return base.neg(a)

        def inv(self, a: tuple[int, ...]) -> tuple[int, ...]:
            self.inversions += 1
            return base.inv(a)

    # Test both small and larger polynomial degrees; the sample points are
    # distinct modulo 2 in the extension field, so all inversions are units.
    for n in (1, 2, 3, 5, 8):
        xs = interp_points(base, n)
        poly = [base.scalar(i + 1) for i in range(n)]
        points = [(x, p_eval(poly, x, base)) for x in xs]
        counter = CountingRing()
        # The CountingRing is structurally compatible with interpolation's
        # ring operations; its only purpose is to count the outer calls.
        got = interpolate(points, counter)  # type: ignore[arg-type]
        assert got == poly
        bound = interpolation_work(n)
        assert counter.multiplications <= bound.coefficient_multiplications
        assert counter.additions <= bound.coefficient_additions_or_subtractions
        assert counter.inversions == bound.coefficient_inversions


def test_paper_precision_envelope_matches_terminal_and_active_regimes() -> None:
    small = ContractorConfig(s=28, precision=7, schedule="paper")
    frames = paper_frame_envelopes(small, 96, 28)
    assert len(frames) == 1 and frames[0].terminal
    assert frames[0].precision == frames[0].child_precision == 7
    assert max_padic_vector_bits(small, frames) == 4 * 5 * 7
    assert recursive_call_bound_from_frames(frames) == recursive_call_bound(small, 96)

    # Symbolic schedule only: NEVER instantiate a Padic of this degree.
    first = ContractorConfig(s=(1 << 131071) + 1, precision=3, schedule="paper")
    frames = paper_frame_envelopes(first, first.s, 40)
    assert len(frames) == 2
    root, child = frames
    assert not root.terminal and child.terminal
    assert root.centers == 7
    assert root.evaluations_per_center == first.s * 7 + 1
    assert root.child_edges == 3 * first.s // 32
    assert root.child_vertices == first.s + 40
    assert root.child_precision > root.precision
    assert child.precision == root.child_precision
    assert max_padic_vector_bits(first, frames) == 4 * 131072 * root.child_precision
    assert recursive_call_bound_from_frames(frames) == recursive_call_bound(first, first.s)


def test_envelopes_reject_invalid_inputs() -> None:
    with pytest.raises(ValueError):
        direct_leaf_work(-1, 2)
    with pytest.raises(ValueError):
        interpolation_work(-1)
    with pytest.raises(ValueError):
        paper_frame_envelopes(ContractorConfig(s=4, precision=3, schedule="micro"), 2, 4)
    with pytest.raises(ValueError):
        paper_frame_envelopes(ContractorConfig(s=4, precision=3), 2, -1)


@pytest.mark.parametrize("box_order", [1, 2, 3, 4])
def test_direct_sudoku_encoding_size_is_exact(box_order: int) -> None:
    from non_exponential_sudoku.sudoku.direct_network import DirectNetwork

    layout = sudoku_direct_encoding_size(box_order)
    puzzle = Puzzle(box_order, (0,) * layout.cells)
    graph = DirectNetwork.from_puzzle(puzzle)
    assert graph.edge_count == layout.wires
    assert len(graph.vertices) == layout.vertices
    assert max(len(vertex.ports) for vertex in graph.vertices) == layout.maximum_degree
    assert graph.wire_bits == layout.bits_per_digit
    assert graph.summary()["count_precision_bits"] == layout.sufficient_count_precision
