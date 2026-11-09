"""Counting-preserving fixed-width-independent CNF representation.

Variables are DIMACS integers 1..nvars, with *declared* variables retained.
Canonicalization removes logically redundant clauses, never variables. In
particular, simplifying a unit clause by deleting its variable would not be a
parsimonious transformation without separately tracking multiplicity.
"""
from __future__ import annotations

from dataclasses import dataclass

from non_exponential_sudoku.runtime.budget import CapacityError


def _literal_order(literal: int) -> tuple[int, bool]:
    return abs(literal), literal < 0


@dataclass(frozen=True, slots=True)
class CNFFormula:
    """Immutable, normalized CNF with exact declared-variable semantics.

    Empty conjunction: 2**nvars solutions; empty clause: zero solutions.
    Tautologies, repeated literals/clauses, and subsumed clauses are removed.
    """

    nvars: int
    clauses: tuple[tuple[int, ...], ...]

    def __post_init__(self) -> None:
        if type(self.nvars) is not int or self.nvars < 0:
            raise ValueError('nvars must be a nonnegative integer')
        normalized: set[tuple[int, ...]] = set()
        for clause in self.clauses:
            literals: set[int] = set()
            tautology = False
            for literal in clause:
                if type(literal) is not int or literal == 0 or abs(literal) > self.nvars:
                    raise ValueError('CNF literals must be nonzero integers in 1..nvars')
                if -literal in literals:
                    tautology = True
                literals.add(literal)
            if not tautology:
                normalized.add(tuple(sorted(literals, key=_literal_order)))
        if () in normalized:
            canonical: tuple[tuple[int, ...], ...] = ((),)
        else:
            ordered = sorted(normalized, key=lambda c: (len(c), tuple(_literal_order(v) for v in c)))
            retained: list[tuple[int, ...]] = []
            covered: list[frozenset[int]] = []
            for clause in ordered:
                content = frozenset(clause)
                if not any(other <= content for other in covered):
                    retained.append(clause)
                    covered.append(content)
            canonical = tuple(retained)
        object.__setattr__(self, 'clauses', canonical)

    def satisfied_mask(self, assignment: int) -> bool:
        """Evaluate against an nvars-bit mask (bit 0 represents variable 1)."""
        if type(assignment) is not int or not 0 <= assignment < (1 << self.nvars):
            raise ValueError('assignment outside the declared Boolean cube')
        for clause in self.clauses:
            if not any(bool(assignment & (1 << (abs(lit) - 1))) == (lit > 0)
                       for lit in clause):
                return False
        return True

    def to_dimacs(self) -> str:
        clauses = [' '.join(map(str, clause)) + (' ' if clause else '') + '0'
                   for clause in self.clauses]
        return '\n'.join([f'p cnf {self.nvars} {len(self.clauses)}', *clauses]) + '\n'

    @classmethod
    def from_dimacs(cls, source: str) -> CNFFormula:
        """Parse strict DIMACS CNF, allowing clauses spanning multiple lines."""
        header: tuple[int, int] | None = None
        clauses: list[tuple[int, ...]] = []
        current: list[int] = []
        for number, line in enumerate(source.splitlines(), 1):
            parts = line.split()
            if not parts or parts[0] == 'c':
                continue
            if header is None:
                if len(parts) != 4 or parts[:2] != ['p', 'cnf']:
                    raise ValueError(f'line {number}: expected p cnf header')
                try:
                    nvars, count = int(parts[2]), int(parts[3])
                except ValueError as exc:
                    raise ValueError(f'line {number}: invalid DIMACS header') from exc
                if nvars < 0 or count < 0:
                    raise ValueError(f'line {number}: negative DIMACS dimensions')
                header = nvars, count
                continue
            for part in parts:
                try:
                    literal = int(part)
                except ValueError as exc:
                    raise ValueError(f'line {number}: invalid literal {part!r}') from exc
                if len(clauses) >= header[1]:
                    raise ValueError(f'line {number}: too many DIMACS clauses')
                if literal == 0:
                    clauses.append(tuple(current))
                    current.clear()
                else:
                    if abs(literal) > header[0]:
                        raise ValueError(f'line {number}: literal exceeds declared nvars')
                    current.append(literal)
        if header is None:
            raise ValueError('missing p cnf header')
        if current or len(clauses) != header[1]:
            raise ValueError('unterminated or missing DIMACS clauses')
        return cls(header[0], tuple(clauses))


def count_bruteforce(
    formula: CNFFormula, *, max_variables: int = 20, max_assignments: int = 1 << 20,
) -> int:
    """Independent exact oracle; *always* exponential and explicitly bounded."""
    if type(max_variables) is not int or type(max_assignments) is not int or max_variables < 0 or max_assignments < 1:
        raise ValueError('oracle limits must be nonnegative/positive integers')
    if formula.nvars > max_variables or (1 << formula.nvars) > max_assignments:
        raise CapacityError('ETH brute-force oracle assignment limit')
    return sum(formula.satisfied_mask(mask) for mask in range(1 << formula.nvars))
