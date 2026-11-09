#!/usr/bin/env python3
"""Parsimonious generalized Sudoku -> 3-CNF -> degree-3 bipartite tensor network.

This is a verified input reduction for the 2026 OpenAI ETH algorithm, NOT an
implementation of that algorithm and NOT a subexponential solver by itself.

For block order b, board side N=b*b. A Boolean variable X[r,c,d] indicates
that cell (r,c) has digit d. The CNF has clauses of width <=3. At-least-one
clauses use definitional OR gates (not equisatisfiable-only arbitrary Tseitin
auxiliaries), so every Sudoku solution has exactly ONE satisfying extension.

The associated tensor graph uses degree <= 3 at all vertices and has a
bipartition.  A path of variable-copy tensors, connected by degree-2 equality
nodes, replaces a high-degree Boolean variable.  Each CNF solution has exactly
one edge assignment of nonzero weight.  Its contraction is therefore #Sudoku.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

DIGITS = '123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'

@dataclass
class CNF:
    nvars: int = 0
    clauses: list[tuple[int, ...]] = field(default_factory=list)
    # (out, left, right); each auxiliary equals OR of its two inputs
    or_gates: list[tuple[int, int, int]] = field(default_factory=list)
    primary: dict[tuple[int, int, int], int] = field(default_factory=dict)

    def var(self) -> int:
        self.nvars += 1
        return self.nvars

    def clause(self, *lits: int) -> None:
        if not 1 <= len(lits) <= 3:
            raise ValueError('Only 1-, 2-, and 3-literal clauses allowed')
        if any(not isinstance(v, int) or not 1 <= abs(v) <= self.nvars for v in lits):
            raise ValueError('Literal outside variable range')
        self.clauses.append(tuple(lits))

    def or_gate(self, left: int, right: int) -> int:
        """z ↔ (x ∨ y) using three clauses, with a unique z per x,y."""
        z = self.var()
        self.clause(-left, z)
        self.clause(-right, z)
        self.clause(left, right, -z)
        self.or_gates.append((z, left, right))
        return z

    def at_least_one(self, vars: list[int]) -> None:
        if not vars:
            raise ValueError('No variables')
        if len(vars) <= 3:
            self.clause(*vars)
            return
        a = self.or_gate(vars[0], vars[1])
        for nxt in vars[2:-1]:
            a = self.or_gate(a, nxt)
        self.clause(a, vars[-1])

    def at_most_one(self, vars: Iterable[int]) -> None:
        xs = list(vars)
        for i, a in enumerate(xs):
            for b in xs[i+1:]:
                self.clause(-a, -b)

    def extend(self, primary_values: dict[int, bool]) -> list[bool]:
        """Get the UNIQUE auxiliary assignment for these primary values."""
        bits = [False] * (self.nvars + 1)
        for var, val in primary_values.items():
            if not 1 <= var <= self.nvars:
                raise ValueError('Unknown primary variable')
            bits[var] = bool(val)
        for z, x, y in self.or_gates:
            bits[z] = bits[x] or bits[y]
        return bits

    def satisfied(self, bits: list[bool]) -> bool:
        if len(bits) != self.nvars + 1:
            raise ValueError('Wrong assignment length')
        return all(any(bits[abs(l)] == (l > 0) for l in clause) for clause in self.clauses)

    def dimacs(self) -> str:
        out = [f'p cnf {self.nvars} {len(self.clauses)}']
        out += [' '.join(map(str, cl)) + ' 0' for cl in self.clauses]
        return '\n'.join(out) + '\n'

@dataclass(frozen=True)
class Puzzle:
    b: int
    entries: tuple[int, ...]

    @classmethod
    def from_text(cls, text: str, b: int = 3) -> 'Puzzle':
        n = b*b
        if n > len(DIGITS):
            raise ValueError('Block size too big for text format')
        chars = [x.upper() for x in text if x.upper() in (DIGITS + '.0')]
        if len(chars) != n*n:
            raise ValueError(f'Expected {n*n} entries, found {len(chars)}')
        entries = tuple(0 if x in '.0' else DIGITS.index(x)+1 for x in chars)
        if any(x > n for x in entries):
            raise ValueError('Digit outside puzzle range')
        return cls(b, entries)

    @property
    def side(self) -> int:
        return self.b*self.b

    def units(self) -> list[list[int]]:
        n = self.side
        u = [[r*n+c for c in range(n)] for r in range(n)]
        u += [[r*n+c for r in range(n)] for c in range(n)]
        u += [[(br*self.b+dr)*n + bc*self.b+dc
               for dr in range(self.b) for dc in range(self.b)]
              for br in range(self.b) for bc in range(self.b)]
        return u

    def valid_solution(self, digits: tuple[int, ...]) -> bool:
        n = self.side
        return (len(digits) == n*n
                and all(set(digits[i] for i in unit) == set(range(1, n+1))
                        for unit in self.units())
                and all(g == 0 or g == s for g, s in zip(self.entries, digits)))

    def encode(self) -> CNF:
        n = self.side
        f = CNF()
        for cell in range(n*n):
            r, c = divmod(cell, n)
            for d in range(1, n+1):
                f.primary[(r, c, d)] = f.var()
        # Each cell chooses precisely one digit.
        for r in range(n):
            for c in range(n):
                vs = [f.primary[r,c,d] for d in range(1, n+1)]
                f.at_least_one(vs)
                f.at_most_one(vs)
        # Every digit occurs at most once in each row / column / box.
        # Since each unit has n cells, that implies exactly once.
        for unit in self.units():
            for d in range(1, n+1):
                vs = [f.primary[divmod(cell, n)+(d,)] for cell in unit]
                f.at_most_one(vs)
        # Unary clue clauses do not introduce nonunique auxiliaries.
        for i, value in enumerate(self.entries):
            if value:
                r, c = divmod(i, n)
                f.clause(f.primary[r,c,value])
        return f

    def witness(self, f: CNF, digits: tuple[int, ...]) -> list[bool]:
        if len(digits) != self.side**2:
            raise ValueError('Wrong solution length')
        vals = {f.primary[r,c,d]: digits[r*self.side+c] == d
                for r in range(self.side) for c in range(self.side)
                for d in range(1, self.side+1)}
        return f.extend(vals)

@dataclass
class TensorGraph:
    """Bipartite, subcubic 0/1 tensor network for a Boolean CNF.

    vertices is a list of (kind, ports, payload) tuples, where ports are edge
    identifiers. Clause tensor: OR of its port bits according to signs.
    Copy tensor: all incident bits equal; a port-free copy contributes 2.
    Link tensor: both incident bits equal. All non-isolated vertices have
    degree <=3; links and clauses are on the left, copies are on the right.
    """
    vertices: list[tuple[str, tuple[int, ...], tuple[int, ...]]]
    edges: int

    @classmethod
    def from_cnf(cls, formula: CNF) -> 'TensorGraph':
        occurrences: list[list[int]] = [[] for _ in range(formula.nvars+1)]
        vertices: list[tuple[str, tuple[int, ...], tuple[int, ...]]] = []
        edges = 0
        for clause in formula.clauses:
            ports = []
            for lit in clause:
                ports.append(edges)
                occurrences[abs(lit)].append(edges)
                edges += 1
            vertices.append(('clause', tuple(ports), tuple(1 if v > 0 else -1 for v in clause)))
        for i in range(1, formula.nvars+1):
            occurrence_ports = occurrences[i]
            if not occurrence_ports:
                vertices.append(('copy', tuple(), tuple()))
                continue
            # Each occurrence gets its own copy tensor with one clause wire
            # and up to two links to adjacent copies. Each link is subdivided
            # with a degree-2 tensor on the clause side, preserving bipartite.
            left_links: list[int | None] = [None] * len(occurrence_ports)
            right_links: list[int | None] = [None] * len(occurrence_ports)
            for j in range(len(occurrence_ports)-1):
                a, b = edges, edges+1
                edges += 2
                vertices.append(('link', (a,b), tuple()))
                right_links[j] = a
                left_links[j+1] = b
            for j, occurrence in enumerate(occurrence_ports):
                ports = [occurrence]
                left_link = left_links[j]
                if left_link is not None:
                    ports.append(left_link)
                right_link = right_links[j]
                if right_link is not None:
                    ports.append(right_link)
                vertices.append(('copy', tuple(ports), tuple()))
        return cls(vertices, edges)

    def validate(self) -> None:
        edge_ends = [0]*self.edges
        for kind, ports, payload in self.vertices:
            if kind not in ('clause','copy','link') or len(ports) > 3:
                raise ValueError('Invalid node')
            if kind == 'link' and len(ports) != 2:
                raise ValueError('Link must be degree two')
            if kind == 'clause' and len(ports) != len(payload):
                raise ValueError('Clause signs mismatch')
            for edge in ports:
                if not 0 <= edge < self.edges:
                    raise ValueError('Invalid edge ID')
                edge_ends[edge] += 1
        if any(deg != 2 for deg in edge_ends):
            raise ValueError('Each edge must have two endpoints')

    def evaluate(self, edge_values: list[bool]) -> int:
        if len(edge_values) != self.edges:
            raise ValueError('Wrong edge count')
        score = 1
        for kind, ports, payload in self.vertices:
            vals = [bool(edge_values[e]) for e in ports]
            if kind == 'clause':
                score *= int(any(v if s > 0 else not v for v, s in zip(vals, payload)))
            elif kind == 'copy':
                score *= int(all(v == vals[0] for v in vals)) if vals else 2
            else:
                score *= int(vals[0] == vals[1])
            if score == 0:
                return 0
        return score

    def witness_edges(self, formula: CNF, assignment: list[bool]) -> list[bool]:
        # Occurrence edge IDs are created first, in clause order.
        vals: list[bool] = []
        for clause in formula.clauses:
            vals.extend(assignment[abs(lit)] for lit in clause)
        # All copy-link edges are created per variable in order; each link
        # connects copies of the same variable and must equal its value.
        for var in range(1, formula.nvars+1):
            occurrences = sum(1 for cl in formula.clauses for lit in cl if abs(lit) == var)
            vals.extend([assignment[var]] * (2*max(0, occurrences-1)))
        assert len(vals) == self.edges
        return vals


def run_cli() -> None:
    parser = argparse.ArgumentParser(description='Count-preserving Sudoku to 3-CNF / subcubic tensor graph (not a SAT solver)')
    parser.add_argument('puzzle', help='Puzzle text (dots = blanks), or @filename')
    parser.add_argument('--box', type=int, default=3, help='Box width: 2 gives 4x4, 3 gives 9x9')
    parser.add_argument('--dimacs', type=Path, help='Write fixed-width DIMACS clauses')
    parser.add_argument('--summary', action='store_true', help='Show counts and properties')
    args = parser.parse_args()
    inp = Path(args.puzzle[1:]).read_text() if args.puzzle.startswith('@') else args.puzzle
    puzzle = Puzzle.from_text(inp, args.box)
    f = puzzle.encode()
    if args.dimacs:
        args.dimacs.write_text(f.dimacs())
    if args.summary or not args.dimacs:
        graph = TensorGraph.from_cnf(f)
        graph.validate()
        print(json.dumps({'box_order': puzzle.b,'side': puzzle.side,
             'cells': puzzle.side**2, 'boolean_variables': f.nvars,
             'cnf_clauses': len(f.clauses), 'max_clause_width': max(map(len, f.clauses)),
             'graph_edges': graph.edges, 'graph_vertices': len(graph.vertices),
             'max_tensor_degree': max(len(p) for _,p,_ in graph.vertices),
             'count_preserving': True, 'paper_algorithm_implemented': False}, indent=2))

if __name__ == '__main__':
    run_cli()
