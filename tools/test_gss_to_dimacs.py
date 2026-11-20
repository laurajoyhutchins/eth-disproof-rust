"""Standard-library regression tests for the GSS to DIMACS conversion."""

from itertools import product
from io import StringIO
import tempfile
from pathlib import Path
import unittest

from gss_to_dimacs import (
    GssFormatError, encode_clauses, main, parse_compact,
    parse_native, variable, write_dimacs,
)


class ConverterTests(unittest.TestCase):
    def test_documented_standard_9x9_example(self):
        rows = [
            "....3....", "7.59....2", "9....1...", ".51....83",
            "...3..5..", "48....76.", "........1", "..8..29..", "....9.62.",
        ]
        puzzle = parse_native("<sudoku>\n" + "\n".join(" ".join(row) for row in rows))
        self.assertEqual(len(puzzle.clues), 81)
        self.assertEqual(len(puzzle.blocks), 27)
        self.assertEqual(puzzle.variables, 729)
        self.assertEqual(puzzle.clues[4], 3)
        self.assertEqual(puzzle.clues[9], 7)
        self.assertEqual(puzzle.clauses, 11988 + sum(c != 0 for c in puzzle.clues))
        data = StringIO()
        write_dimacs(puzzle, data)
        lines = data.getvalue().splitlines()
        self.assertEqual(lines[2], f"p cnf 729 {puzzle.clauses}")
        self.assertEqual(len(lines) - 3, puzzle.clauses)
        self.assertTrue(all(line.endswith(" 0") for line in lines[3:]))

    def test_custom_matrix_four_by_four_with_pattern_and_quote(self):
        source = """<size>16
<blocksize>4
<rowblocks>
<colblocks>
<matrix>
1 1 2 2
1 1 2 2
3 3 4 4
3 3 4 4
<pattern>|.|
<emptychar>0
<sudoku>
"example: |4| must be ignored" 
|1| |2| |3| |4|
|3| |4| |1| |2|
|2| |1| |4| |3|
|4| |3| |2| |1|
<endsudoku>
"""
        puzzle = parse_native(source)
        self.assertEqual(puzzle.variables, 64)
        self.assertEqual(len(puzzle.blocks), 12)
        self.assertEqual(puzzle.clues[:4], (1, 2, 3, 4))
        self.assertEqual(sum(1 for b in puzzle.blocks if b == (0, 1, 4, 5)), 1)
        model = {variable(i, v, 4) for i, v in enumerate(puzzle.clues)}
        self.assertTrue(all(any((literal > 0) == (abs(literal) in model)
                                for literal in clause)
                            for clause in encode_clauses(puzzle)))

    def test_wide_cells_and_diagonal(self):
        text = "<size>256\n<blocksize>16\n<standardblocks>\n<downdiagblock>\n<sudoku>\n"
        text += "\n".join(" ".join([".."] * 16) for _ in range(16))
        puzzle = parse_native(text)
        self.assertEqual(puzzle.variables, 4096)
        self.assertEqual(len(puzzle.blocks), 49)
        self.assertEqual(puzzle.clues, (0,) * 256)

    def test_matrix_only_custom_non_grid(self):
        puzzle = parse_native("""<size>4
<blocksize>2
<block> 1 2
<block> 3 4
<block> 1 3
<block> 2 4
<sudoku>
. . . .
""")
        clauses = list(encode_clauses(puzzle))
        # Exhaust all 2^8 Boolean models, comparing to an independent
        # direct enumeration of 2^4 grids and the original all-different rule.
        satisfying = []
        for bits in product((False, True), repeat=8):
            if all(any(bits[abs(lit) - 1] if lit > 0 else not bits[-lit - 1]
                       for lit in clause) for clause in clauses):
                satisfying.append(bits)
        solutions = []
        for grid in product((1, 2), repeat=4):
            if all({grid[i] for i in block} == {1, 2} for block in puzzle.blocks):
                solutions.append(grid)
        self.assertEqual(len(satisfying), 2)
        self.assertEqual(len(solutions), 2)
        decoded = [tuple(next(d for d in (1, 2) if bits[variable(i, d, 2) - 1])
                         for i in range(4)) for bits in satisfying]
        self.assertEqual(set(decoded), set(solutions))

    def test_compact_multiple(self):
        source = "# comments\n" + "." * 81 + "\n" + "0" * 80 + "7\n"
        puzzles = parse_compact(source)
        self.assertEqual(len(puzzles), 2)
        self.assertEqual(puzzles[0].clauses, 11988)
        self.assertEqual(puzzles[1].clauses, 11989)
        with tempfile.TemporaryDirectory() as tmp:
            src = Path(tmp) / "many.txt"
            src.write_text(source)
            self.assertEqual(main([str(src), "--format", "compact"]), 0)
            files = sorted((Path(tmp) / "many_cnf").glob("*.cnf"))
            self.assertEqual(len(files), 2)
            self.assertTrue(files[1].read_text().startswith("c Generic"))

    def test_cli_auto_detects_native_format(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = Path(tmp) / "puzzle.txt"
            src.write_text("<size>4\n<blocksize>2\n<rowblocks>\n"
                           "<colblocks>\n<sudoku>\n. . . .\n")
            self.assertEqual(main([str(src)]), 0)
            self.assertIn("p cnf 8 24", src.with_suffix(".cnf").read_text())
            with self.assertRaises(SystemExit):
                main([str(src), "-o", str(src)])

    def test_refuses_silent_loss_of_constraints(self):
        with self.assertRaises(GssFormatError):
            parse_native("<size>4\n<blocksize>2\n<sudoku>\n. . . .")
        with self.assertRaises(GssFormatError):
            parse_native("<size>4\n<blocksize>2\n<block> 1 1\n<sudoku>\n. . . .")
        with self.assertRaises(GssFormatError):
            parse_native("<size>4\n<blocksize>2\n<block> 1 2\n<matrix>\n1 1 . .\n<sudoku>\n. . . .")
        with self.assertRaises(GssFormatError):
            parse_native("<sudoku>\n" + "." * 80)
        with self.assertRaises(GssFormatError):
            parse_compact("." * 80)


if __name__ == "__main__":
    unittest.main()
