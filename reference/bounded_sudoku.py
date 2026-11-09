"""Exact bounded-degree Boolean tensor network for generalized Sudoku.

This adapter preserves the existing 3-CNF/TensorGraph reduction, including
its unique auxiliary extensions. It is useful for testing the *degree-3*
conditions of the ETH contraction construction, not for replacing the much
smaller fused-band Sudoku input when doing practical small-puzzle counts.
"""
from non_exponential_sudoku.sudoku.three_cnf import TensorGraph, Puzzle
from non_exponential_sudoku.core.network import Network, Vertex


def from_tensor_graph(graph: TensorGraph) -> Network:
    graph.validate()
    left, right = [], []
    for number, (kind, ports, payload) in enumerate(graph.vertices):
        if kind == 'clause':
            signs = payload
            def oracle(bits, ring, signs=signs):
                return ring.one if any((bit == 1) if sign > 0 else (bit == 0)
                                       for bit, sign in zip(bits, signs)) else ring.zero
            left.append(Vertex(f'clause:{number}', ports, oracle))
        elif kind == 'link':
            def oracle(bits, ring):
                return ring.one if bits[0] == bits[1] else ring.zero
            left.append(Vertex(f'link:{number}', ports, oracle))
        elif kind == 'copy':
            def oracle(bits, ring):
                if not bits:
                    return ring.scalar(2)
                return ring.one if all(b == bits[0] for b in bits) else ring.zero
            right.append(Vertex(f'copy:{number}', ports, oracle))
        else:
            raise AssertionError(kind)
    network = Network(left, right, graph.edges)
    network.validate()
    return network


def from_puzzle(puzzle: Puzzle) -> Network:
    return from_tensor_graph(TensorGraph.from_cnf(puzzle.encode()))
