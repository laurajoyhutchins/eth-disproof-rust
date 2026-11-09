#!/usr/bin/env python3
"""Generalized Sudoku -> Boolean tensor-network INPUT for OpenAI Appendix D.

The paper's Boolean tensor contraction theorem applies directly to networks
of this form; in particular, it requires no CNF or SAT reduction.  The output
here is the network and its (polynomial-time) local entry oracles, NOT an
implementation of the paper's recursive contractor.

For side n=b^2 each cell is a t=ceil(log2 n)-bit digit in [0,n-1].  There are
three copies of each bit, one for the row, column, and box constraints, with
a cell tensor forcing all three copies equal. Each unit factor checks that
n encoded digits are pairwise distinct. A clue restricts its cell tensor.

All vertices are bipartite: cells on side A, row/col/box units on side B.
Each edge is one Boolean bit; |E|=3*n^2*t. Maximum tensor degree=n*t or 3*t.
The contraction is exactly the number of Sudoku solutions, with no extra
multiplicity: every Sudoku grid has exactly one edge assignment of weight 1.
"""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from .three_cnf import Puzzle, DIGITS

@dataclass(frozen=True)
class Vertex:
    kind: str
    name: str
    ports: tuple[int, ...]
    clue: int = 0
    
@dataclass
class DirectNetwork:
    puzzle: Puzzle
    vertices: list[Vertex]
    edge_count: int
    wire_bits: int
    edge_cells: tuple[tuple[int,int], ...]  # (cell index, bit index) for each edge

    @classmethod
    def from_puzzle(cls,puzzle: Puzzle) -> 'DirectNetwork':
        n=puzzle.side
        t=max(1,(n-1).bit_length())
        units=puzzle.units()
        # First n row units, then n col units, then n box units.
        ports_unit: list[list[int]]=[[] for _ in units]
        ports_cell: list[list[int]]=[[] for _ in range(n*n)]
        edge_cells: list[tuple[int, int]]=[]
        for c in range(n*n):
            row,col=divmod(c,n)
            box=(row//puzzle.b)*puzzle.b+(col//puzzle.b)
            selected=(row,n+col,2*n+box)
            for uid in selected:
                for bit in range(t):
                    edge=len(edge_cells)
                    ports_unit[uid].append(edge)
                    ports_cell[c].append(edge)
                    edge_cells.append((c,bit))
        # The construction visits cells in reading order; row/col units
        # receive cells in unit order. Boxes also receive row-major order.
        vertices = [Vertex('cell',f'cell:{c}',tuple(ports_cell[c]), puzzle.entries[c])
                    for c in range(n*n)]
        vertices += [Vertex('unit',f'{"row" if i<n else "column" if i<2*n else "box"}:{i % n}',tuple(ports_unit[i]))
                     for i in range(3*n)]
        network=cls(puzzle,vertices,len(edge_cells),t,tuple(edge_cells))
        network.validate()
        return network

    @staticmethod
    def decode(bits: list[int] | tuple[int,...]) -> int:
        return sum(int(b)<<i for i,b in enumerate(bits))

    def local_entry(self, vertex: Vertex, edge_assignment: list[int] | tuple[int, ...]) -> int:
        """Return one tensor entry from its incident port bits."""
        vals=[edge_assignment[e] for e in vertex.ports]
        if len(vals)!=len(vertex.ports) or any(v not in (0,1,False,True) for v in vals):
            raise ValueError('Non-Boolean port')
        t=self.wire_bits
        if vertex.kind=='cell':
            a= self.decode(vals[:t])
            b= self.decode(vals[t:2*t])
            c= self.decode(vals[2*t:3*t])
            if not (a==b==c and a<self.puzzle.side):
                return 0
            return int(vertex.clue==0 or vertex.clue==a+1)
        if vertex.kind=='unit':
            dig=[self.decode(vals[i:i+t]) for i in range(0,len(vals),t)]
            return int(len(dig)==self.puzzle.side and len(set(dig))==self.puzzle.side)
        raise ValueError('Unexpected tensor kind')

    def evaluate(self, edge_assignment: list[int] | tuple[int,...]) -> int:
        if len(edge_assignment)!=self.edge_count:
            raise ValueError('Wrong number of wire bits')
        for vertex in self.vertices:
            if not self.local_entry(vertex,edge_assignment):
                return 0
        return 1

    def witness_edges(self, digits: tuple[int,...]) -> list[int]:
        if len(digits)!=self.puzzle.side**2:
            raise ValueError('Wrong number of cells')
        return [(digits[cell]-1 >> bit) & 1 for cell,bit in self.edge_cells]

    def validate(self) -> None:
        n=self.puzzle.side
        t=self.wire_bits
        if self.edge_count!=3*n*n*t:
            raise AssertionError('Bad edge count')
        if len(self.vertices)!=n*n+3*n:
            raise AssertionError('Bad vertex count')
        counts=[0]*self.edge_count
        for v in self.vertices:
            if len(v.ports)!=(3*t if v.kind=='cell' else n*t):
                raise AssertionError('Unexpected tensor arity')
            for edge in v.ports:
                if not 0<=edge<self.edge_count:
                    raise AssertionError('Out of bounds wire')
                counts[edge]+=1
        if any(c!=2 for c in counts):
            raise AssertionError('Every edge must connect two vertices')
        # This input graph is bipartite by construction: every bit visits
        # precisely one cell and one unit factor.

    def summary(self) -> dict[str, int | bool]:
        n=self.puzzle.side
        s=self.edge_count
        Delta=max(n*self.wire_bits,3*self.wire_bits)
        return {'box_order':self.puzzle.b,'side':n,'cells':n*n,
                'wire_bits_per_digit':self.wire_bits,
                'boolean_wires':s,'tensor_vertices':len(self.vertices),
                'max_tensor_degree':Delta,
                'count_precision_bits':n*n*self.wire_bits+1,
                'within_s_point_nine_bound':Delta<=__import__('math').ceil(s**0.9),
                'exact_solution_count_representation': True,
                'subexponential_contractor_implemented': False}


def main() -> None:
    arg=argparse.ArgumentParser(description='Build Appendix D-compatible Sudoku tensor-network input')
    arg.add_argument('puzzle',help='Puzzle text (dots for blanks), or @file')
    arg.add_argument('--box',type=int,default=3)
    arg.add_argument('--json',type=Path,help='Write explicit graph and vertex entries as JSON')
    args=arg.parse_args()
    puzzle=Puzzle.from_text(Path(args.puzzle[1:]).read_text() if args.puzzle.startswith('@') else args.puzzle,args.box)
    n=DirectNetwork.from_puzzle(puzzle)
    if args.json:
        args.json.write_text(json.dumps({'summary':n.summary(),
              'vertices':[{'kind':v.kind,'name':v.name,'ports':list(v.ports),'clue':v.clue} for v in n.vertices],
              'edge_cell_bits':list(map(list,n.edge_cells))},indent=2)+'\n')
    print(json.dumps(n.summary(),indent=2))

if __name__=='__main__':
    main()
