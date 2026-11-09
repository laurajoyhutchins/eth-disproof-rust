"""One-way adapter from the pre-existing parsimonious Sudoku CNF encoding."""
from __future__ import annotations

from non_exponential_sudoku.sudoku.three_cnf import CNF, Puzzle
from .cnf import CNFFormula


def from_sudoku_cnf(formula: CNF) -> CNFFormula:
    """Keep all Sudoku gate variables; normalizing never projects them away."""
    return CNFFormula(formula.nvars, tuple(formula.clauses))


def from_sudoku_puzzle(puzzle: Puzzle) -> CNFFormula:
    return from_sudoku_cnf(puzzle.encode())
