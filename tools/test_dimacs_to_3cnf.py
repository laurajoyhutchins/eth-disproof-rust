"""Independent finite model comparison for the #SAT-preserving 3-CNF adapter."""
from itertools import product
from pathlib import Path
import tempfile
import unittest

from dimacs_to_3cnf import DimacsError, main, make_3cnf, parse_dimacs
from gss_to_dimacs import encode_clauses, parse_native


def satisfies(clauses, values):
    return all(any((values[abs(lit) - 1] if lit > 0 else not values[-lit - 1])
                   for lit in clause) for clause in clauses)


class Dimacs3CnfTests(unittest.TestCase):
    def verify_unique_extension(self, variables, clauses):
        width, translated = make_3cnf(variables, clauses)
        self.assertTrue(all(len(clause) <= 3 for clause in translated))
        self.assertTrue(all(0 < abs(lit) <= width for c in translated for lit in c))
        self.assertEqual(width, variables + sum(max(len(c) - 3, 0) for c in clauses))
        for assignment in product((False, True), repeat=variables):
            number = sum(satisfies(translated, assignment + extra)
                         for extra in product((False, True), repeat=width - variables))
            self.assertEqual(number, int(satisfies(clauses, assignment)),
                             (clauses, assignment))
        return width, translated

    def test_long_clauses_have_unique_extensions(self):
        self.verify_unique_extension(4, ((1, 2, 3, 4),))
        self.verify_unique_extension(4, ((-1, 2, -3, 4),))
        self.verify_unique_extension(5, ((1, -2, 3, -4, 5),))
        self.verify_unique_extension(5, ((1, 2, 3, 4), (-1, -2, 3, -4, 5)))

    def test_empty_clauses_and_unused_declared_variables(self):
        self.verify_unique_extension(3, ((),))
        self.verify_unique_extension(3, ())
        self.verify_unique_extension(4, ((1, -1, 2, 3),))
        self.verify_unique_extension(4, ((1, 1, 2, 3),))

    def test_gss_2x2_matches_independent_grid_enumeration(self):
        src = """<size>4
<blocksize>2
<block> 1 2
<block> 3 4
<block> 1 3
<block> 2 4
<sudoku>
. . . .
"""
        puzzle = parse_native(src)
        original = tuple(encode_clauses(puzzle))
        _, converted = self.verify_unique_extension(puzzle.variables, original)
        models = sum(satisfies(original, assignment)
                     for assignment in product((False, True), repeat=8))
        legal_grids = sum(grid[0] != grid[1] and grid[2] != grid[3]
                          and grid[0] != grid[2] and grid[1] != grid[3]
                          for grid in product((1, 2), repeat=4))
        self.assertEqual(models, legal_grids)
        self.assertEqual(models, 2)
        self.assertEqual(original, converted)

    def test_generated_empty_four_by_four_has_strict_width_three(self):
        fixture = Path(__file__).resolve().parents[1] / "eth/fixtures/gss/empty_4x4.gss"
        puzzle = parse_native(fixture.read_text())
        self.assertEqual((puzzle.variables, puzzle.clauses), (64, 448))
        width, translated = make_3cnf(puzzle.variables, tuple(encode_clauses(puzzle)))
        self.assertEqual((width, len(translated)), (128, 640))
        self.assertTrue(all(len(c) <= 3 for c in translated))

    def test_strict_dimacs_validation_and_cli(self):
        for text in ("p cnf 4 2\n1 2 0\n", "p cnf 2 1\n3 0\n",
                     "p cnf 2 1\n1\n", "p cnf 2 0\n1 0\n", "p cnf 2 1\n1 0\n2 0\n"):
            with self.subTest(text=text), self.assertRaises(DimacsError):
                parse_dimacs(text)
        self.assertEqual(parse_dimacs("c hi\np cnf 3 1\n1 -2\n3 0\n"),
                         (3, ((1, -2, 3),)))
        with tempfile.TemporaryDirectory() as tmp:
            source, target = Path(tmp) / "input.cnf", Path(tmp) / "output.cnf"
            source.write_text("p cnf 4 1\n1 2 3 4 0\n")
            self.assertEqual(main([str(source), "-o", str(target)]), 0)
            n, clauses = parse_dimacs(target.read_text())
            self.assertEqual((n, len(clauses)), (5, 4))
            self.assertEqual(max(map(len, clauses)), 3)
            with self.assertRaises(SystemExit):
                main([str(source), "-o", str(source)])


if __name__ == "__main__":
    unittest.main()
