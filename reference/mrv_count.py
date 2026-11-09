"""Independent Sudoku exact-count oracle for *tests and benchmarks only*.

Classic minimum-remaining-values backtracking over Sudoku row/column/box
masks. Unlike the production frontier counter, it enumerates the search tree,
and is deliberately never imported by the solver. Explicitly caps tree nodes.
"""
from __future__ import annotations

from non_exponential_sudoku.sudoku.three_cnf import Puzzle


def count_mrv_reference(puzzle: Puzzle, *, max_nodes: int = 100_000
                        ) -> tuple[int, int]:
    n, b = puzzle.side, puzzle.b
    full = (1 << n) - 1
    row, column, box = [0] * n, [0] * n, [0] * n
    positions = tuple((cell // n, cell % n,
                       (cell // n // b) * b + (cell % n) // b)
                      for cell in range(n * n))
    free: list[int] = []
    for cell, digit in enumerate(puzzle.entries):
        r, c, q = positions[cell]
        if not digit:
            free.append(cell)
            continue
        bit = 1 << (digit - 1)
        if bit & (row[r] | column[c] | box[q]):
            return 0, 0
        row[r] |= bit
        column[c] |= bit
        box[q] |= bit

    visited = 0

    def recurse(remaining: list[int]) -> int:
        nonlocal visited
        visited += 1
        if visited > max_nodes:
            raise RuntimeError('Independent reference search node limit')
        if not remaining:
            return 1
        chosen = -1
        choices = 0
        smallest = n + 1
        for i, cell in enumerate(remaining):
            r, c, q = positions[cell]
            options = full & ~(row[r] | column[c] | box[q])
            count = options.bit_count()
            if count < smallest:
                chosen, choices, smallest = i, options, count
                if count <= 1:
                    break
        if not choices:
            return 0
        cell = remaining[chosen]
        r, c, q = positions[cell]
        rest = remaining[:chosen] + remaining[chosen + 1:]
        result = 0
        while choices:
            bit = choices & -choices
            choices ^= bit
            row[r] |= bit
            column[c] |= bit
            box[q] |= bit
            result += recurse(rest)
            row[r] ^= bit
            column[c] ^= bit
            box[q] ^= bit
        return result

    return recurse(free), visited
