"""Encode a generalized Sudoku as a finite-oracle contraction network.

The independent exponential evaluator and synthetic crossing graph live in
reference/sudoku_network_oracle.py, outside the production package.
"""
from __future__ import annotations

from ..core.network import Network, Vertex
from .three_cnf import Puzzle
from .input_oracles import CellEntryOracle, UnitEntryOracle

def sudoku_network(puzzle: Puzzle) -> Network:
    """Convert direct_network.py's *parsimonious* Sudoku network to this ABI."""
    from .direct_network import DirectNetwork, Vertex as DirectVertex
    original=DirectNetwork.from_puzzle(puzzle)
    sides: dict[str, list[Vertex]] = {'cell':[], 'unit':[]}
    width = original.wire_bits
    side = puzzle.side

    def compile_oracle(vertex: DirectVertex) -> Vertex:
        # The only admitted input callbacks are finite immutable source
        # programs. Independent DirectNetwork.local_entry remains the oracle
        # for count-preserving semantic tests.
        ports = tuple(vertex.ports)
        if vertex.kind == 'cell':
            return Vertex(vertex.name, ports,
                          CellEntryOracle(side, width, vertex.clue))
        if vertex.kind == 'unit':
            return Vertex(vertex.name, ports, UnitEntryOracle(side, width))
        raise ValueError('Unexpected tensor kind')

    for vertex in original.vertices:
        sides[vertex.kind].append(compile_oracle(vertex))
    net=Network(sides['cell'],sides['unit'],original.edge_count)
    net.validate()
    return net
