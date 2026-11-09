#!/usr/bin/env python3
"""Lossless generalized-Sudoku tensor encoding with ONE Boolean wire per bit.

All cells in the same horizontal box band form a left tensor: check its b
rows, its b boxes and its clues. Each column is a right tensor. The bit of
each cell's digit crosses this bipartition once, so one legal Sudoku solution
corresponds to exactly one nonzero network edge assignment. Tensor vertices
are polynomial-time local oracles; their tables are never materialized.

For side n=b*b and t=ceil(log2 n), this gives n*n*t edges rather than
3*n*n*t, without solving any Sudoku constraints in advance.
"""
from __future__ import annotations
from dataclasses import dataclass
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from non_exponential_sudoku.core.network import Network, Vertex


@dataclass(frozen=True)
class BandNetwork:
    puzzle:Puzzle
    net:Network
    edge_cells:tuple[tuple[int,int], ...]

    @classmethod
    def from_puzzle(cls,puzzle:Puzzle):
        b=puzzle.b;n=puzzle.side;t=max(1,(n-1).bit_length())
        left_ports=[[] for _ in range(b)]
        right_ports=[[] for _ in range(n)]
        left_cells=[[] for _ in range(b)]
        right_cells=[[] for _ in range(n)]
        edge_cells=[]
        # Assign an edge for every (cell, digit bit), one for its band and
        # exactly one for its column. Both oracles see the same digit bits.
        for cell in range(n*n):
            row,col=divmod(cell,n);band=row//b
            left_cells[band].append(cell)
            right_cells[col].append(cell)
            for k in range(t):
                e=len(edge_cells)
                edge_cells.append((cell,k))
                left_ports[band].append(e)
                right_ports[col].append(e)

        def make_band_oracle(cells):
            cells=tuple(cells)
            # The cells are row-major within the band: b rows of n cells.
            clues=tuple(puzzle.entries[c] for c in cells)
            def oracle(bits,R):
                if len(bits)!=len(cells)*t:raise ValueError('Band arity mismatch')
                values=[1+sum(bits[i*t+k]<<k for k in range(t))
                        for i in range(len(cells))]
                if any(v>n or (clue!=0 and clue!=v)
                       for v,clue in zip(values,clues)):
                    return R.zero
                # Rows: b disjoint sequences of n digits.
                if any(len(set(values[i*n:(i+1)*n]))!=n for i in range(b)):
                    return R.zero
                # Boxes within this band: each has b consecutive columns
                # across all b rows.
                for box_col in range(b):
                    members=[values[r*n+box_col*b+c]
                             for r in range(b) for c in range(b)]
                    if len(set(members))!=n:return R.zero
                return R.one
            return oracle

        def make_col_oracle(cells):
            cells=tuple(cells)
            def oracle(bits,R):
                if len(bits)!=len(cells)*t:raise ValueError('Column arity mismatch')
                values=[1+sum(bits[i*t+k]<<k for k in range(t))
                        for i in range(len(cells))]
                return R.one if all(v<=n for v in values) and len(set(values))==n else R.zero
            return oracle

        left=[Vertex(f'band:{i}',tuple(left_ports[i]),make_band_oracle(left_cells[i]))
              for i in range(b)]
        right=[Vertex(f'column:{i}',tuple(right_ports[i]),make_col_oracle(right_cells[i]))
               for i in range(n)]
        network=Network(left,right,len(edge_cells))
        network.validate()
        return cls(puzzle,network,tuple(edge_cells))

    def witness_edges(self,digits:tuple[int,...]):
        if len(digits)!=self.puzzle.side**2:raise ValueError('Bad digit count')
        return tuple(((digits[cell]-1)>>bit)&1 for cell,bit in self.edge_cells)

    def evaluate(self,bits:tuple[int,...]):
        from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
        if len(bits)!=len(self.edge_cells):raise ValueError('Wrong wire count')
        R=Padic(2,modulus_polynomial(2),3)
        return int(all(v.oracle(tuple(bits[e] for e in v.ports),R)!=R.zero
                       for v in self.net.left+self.net.right))

    def summary(self):
        n=self.puzzle.side;t=max(1,(n-1).bit_length());b=self.puzzle.b
        s=len(self.edge_cells)
        return {'side':n,'band_factors':b,'column_factors':n,
                'wires':s,'direct_wires':3*s,'max_degree':max(b*n*t,n*t),
                'parsimony':'exact: one edge assignment per legal grid'}
