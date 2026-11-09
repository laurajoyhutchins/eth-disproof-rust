from __future__ import annotations

from itertools import product
from typing import cast
from ..core.network import Network, Vertex, simple_network, TensorRing
from ..core.algebra import Padic
from ..core.jets import NestedRing
from ..core.lazy_coefficients import NestedCoords
from ..core.packing import Packing
from .three_cnf import Puzzle
from ..contraction.packets import cauchy_values, PacketRing
from ..runtime.budget import CapacityError

def sudoku_network(puzzle: Puzzle) -> Network:
    """Convert direct_network.py's *parsimonious* Sudoku network to this ABI."""
    from .direct_network import DirectNetwork, Vertex as DirectVertex
    original=DirectNetwork.from_puzzle(puzzle)
    sides: dict[str, list[Vertex]] = {'cell':[], 'unit':[]}
    width = original.wire_bits
    side = puzzle.side

    def decode(bits: tuple[int, ...], start: int) -> int:
        return sum(bit << offset for offset, bit in enumerate(bits[start:start + width]))

    def compile_oracle(vertex: DirectVertex) -> Vertex:
        # Compile a local Boolean tensor, not a full network assignment.
        # The original DirectNetwork evaluator remains the independent oracle.
        ports = tuple(vertex.ports)
        if vertex.kind == 'cell':
            clue = vertex.clue

            def cell_oracle(bits: tuple[int, ...], R: TensorRing) -> NestedCoords:
                if len(bits) != len(ports) or any(bit not in (0, 1, False, True) for bit in bits):
                    raise ValueError('Non-Boolean port')
                a = decode(bits, 0)
                b = decode(bits, width)
                c = decode(bits, 2 * width)
                return R.scalar(int(a == b == c and a < side and (clue == 0 or clue == a + 1)))

            return Vertex(vertex.name, ports, cell_oracle)
        if vertex.kind == 'unit':
            def unit_oracle(bits: tuple[int, ...], R: TensorRing) -> NestedCoords:
                if len(bits) != len(ports) or any(bit not in (0, 1, False, True) for bit in bits):
                    raise ValueError('Non-Boolean port')
                digits = (decode(bits, start) for start in range(0, len(bits), width))
                return R.scalar(int(len(ports) == side * width and len(set(digits)) == side))
            return Vertex(vertex.name, ports, unit_oracle)
        raise ValueError('Unexpected tensor kind')

    for vertex in original.vertices:
        sides[vertex.kind].append(compile_oracle(vertex))
    net=Network(sides['cell'],sides['unit'],original.edge_count)
    net.validate()
    return net


def independently_evaluate_F(net: Network, packing: Packing, t: int,
                             z: NestedCoords, R: TensorRing) -> NestedCoords:
    """Independent 2^(2M) evaluator for tests ONLY; not solver path."""
    if net.edges>7:raise CapacityError('Oracle comparison limited to 7 edges')
    L=1<<packing.a
    B=cast(NestedRing, R)
    W=cast(dict[int, NestedCoords], cauchy_values(t,z,cast(PacketRing,R),L))
    ans=B.zero
    for Ys in product((0,1),repeat=net.edges):
        row=B.one
        for v in net.left:
            row=B.mul(row,v.oracle(tuple(Ys[k] for k in v.ports),R))
        if row==B.zero:continue
        for Xs in product((0,1),repeat=net.edges):
            weight=row
            for vert in net.right:
                weight=B.mul(weight,vert.oracle(tuple(Xs[k] for k in vert.ports),R))
            if weight==B.zero:continue
            for pkt in packing.packets:
                for x,edge in enumerate(pkt.slots):
                    if edge is None: continue
                    WX=B.zero
                    for y,col_edge in enumerate(pkt.slots):
                        if col_edge is not None and Xs[col_edge]:
                            WX=B.add(WX,W[y-x])
                    weight=B.mul(weight,WX if Ys[edge] else B.sub(B.one,WX))
            ans=B.add(ans,weight)
    return ans


def port_graph_with_cross_mode() -> Network:
    """Single actual crossing packet; a microtest for nonzero beta terms."""
    return simple_network(1,
        [([0],{(0,):0,(1,):1})],
        [([0],{(0,):0,(1,):1})])
