"""Shift-left invariants: compiled oracles, valuation reuse, support-preserving preprocessing."""
from __future__ import annotations

from random import Random
from unittest.mock import patch

import pytest

from benchmarks.recursive_cases import get_case
from non_exponential_sudoku.contraction import engine as contraction_engine
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.sudoku.direct_network import DirectNetwork
from non_exponential_sudoku.sudoku.encoding import sudoku_network
from non_exponential_sudoku.sudoku.state import support_projected_domains
from non_exponential_sudoku.sudoku.frontier import count_frontier
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.local_support import projected_domains

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize("block", (1, 2, 3))
def test_local_tensor_oracles_use_only_local_bits(block: int) -> None:
    n = block * block
    entries = (1,) + (0,) * (n * n - 1)
    puzzle = Puzzle(block, entries)
    direct = DirectNetwork.from_puzzle(puzzle)
    compiled = sudoku_network(puzzle)
    ring = Padic(5, modulus_polynomial(5), 5)
    rng = Random(711 + block)
    old_vertices = direct.vertices
    new_vertices = compiled.left + compiled.right
    assert [v.name for v in old_vertices] == [v.name for v in new_vertices]
    samples = []
    for old, new in zip(old_vertices, new_vertices):
        cases = [(0,) * len(old.ports), (1,) * len(old.ports)]
        cases.extend(tuple(rng.randrange(2) for _ in old.ports) for _ in range(4))
        for bits in cases:
            assignment = [0] * direct.edge_count
            for edge, value in zip(old.ports, bits):
                assignment[edge] = value
            expected = direct.local_entry(old, assignment)
            assert new.oracle(bits, ring) == ring.scalar(expected)
            samples.append((new, bits, expected))
    # The compiled closure must not use the full-size DirectNetwork evaluator.
    with patch.object(DirectNetwork, "local_entry",
                      side_effect=AssertionError("network-wide local entry called")):
        for vertex, bits, expected in samples:
            assert vertex.oracle(bits, ring) == ring.scalar(expected)


def test_mode_catalog_compiled_once_per_valuation(monkeypatch: pytest.MonkeyPatch) -> None:
    case = get_case("parity-2wire", "plans")
    original = contraction_engine.mode_catalog
    calls: list[tuple[int, int]] = []

    def count_catalog(net, packing, t, precision, *args, **kwargs):
        calls.append((t, precision))
        return original(net, packing, t, precision, *args, **kwargs)

    monkeypatch.setattr(contraction_engine, "mode_catalog", count_catalog)
    solver = contraction_engine.ContractionEngine(case.config)
    assert solver.contract(case.network)[0] == case.expected
    # a=1 means two nonzero centers t=-1,+1, both v2(t)=0.
    assert len(calls) == 1, calls


def test_matching_projection_preserves_exact_counts() -> None:
    puzzles = (
        Puzzle(2, (0,) * 16),
        Puzzle(2, (1, 0, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)),
        Puzzle(2, (1,) * 16),
    )
    for puzzle in puzzles:
        expected = count_frontier(puzzle).count
        projected = support_projected_domains(puzzle)
        if projected is None:
            assert expected == 0
            continue
        reference, _ = projected_domains(puzzle, method="enhanced")
        assert projected == reference
        assert count_frontier(puzzle, domains=projected).count == expected
        assert count_frontier(puzzle, projection="matching").count == expected
    target = puzzles[1]
    simple = count_frontier(target)
    matching = count_frontier(target, projection="matching")
    assert matching.count == simple.count
    assert matching.stats.candidate_choices <= simple.stats.candidate_choices
