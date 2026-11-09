"""The production Sudoku encoder does not ship independent exponential oracles."""
from __future__ import annotations

from non_exponential_sudoku.sudoku import encoding
from reference.sudoku_network_oracle import (
    independently_evaluate_F, port_graph_with_cross_mode,
)


def test_test_only_sudoku_oracles_are_not_runtime_entrypoints() -> None:
    assert callable(encoding.sudoku_network)
    assert callable(independently_evaluate_F)
    assert callable(port_graph_with_cross_mode)
    assert not hasattr(encoding, "independently_evaluate_F")
    assert not hasattr(encoding, "port_graph_with_cross_mode")
