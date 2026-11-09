"""Independent finite reference checks for Sudoku contraction deformations.

These are deliberately exponential or synthetic, not production solver paths.
Do not import them from the runtime's Sudoku encoding module.
"""
from __future__ import annotations

from itertools import product
from typing import cast
from non_exponential_sudoku.core.network import Network, simple_network, TensorRing
from non_exponential_sudoku.core.jets import NestedRing
from non_exponential_sudoku.core.lazy_coefficients import NestedCoords
from non_exponential_sudoku.core.packing import Packing
from non_exponential_sudoku.contraction.packets import cauchy_values, PacketRing
from non_exponential_sudoku.runtime.budget import CapacityError

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
