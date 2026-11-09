"""ETH-001: independent Boolean truth-table and DIMACS contracts."""
from __future__ import annotations

from itertools import combinations, product
from random import Random

import pytest

from non_exponential_sudoku.eth import (CNFFormula, count_bruteforce,
                                        from_sudoku_cnf, from_sudoku_puzzle)
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.sudoku.three_cnf import CNF, Puzzle

pytestmark = pytest.mark.checkpoint


def independent_count(nvars: int, clauses: tuple[tuple[int, ...], ...]) -> int:
    """Independent truth-table specification using bit tuples, not CNF methods."""
    return sum(all(any((values[abs(lit) - 1] if lit > 0 else not values[abs(lit) - 1])
                       for lit in clause) for clause in clauses)
               for values in product((False, True), repeat=nvars))


def test_empty_and_contradictory_formulas_keep_declared_variables() -> None:
    assert count_bruteforce(CNFFormula(0, ())) == 1
    assert count_bruteforce(CNFFormula(4, ())) == 16
    assert count_bruteforce(CNFFormula(4, ((),))) == 0
    assert count_bruteforce(CNFFormula(4, ((1,), (-1,)))) == 0
    assert count_bruteforce(CNFFormula(4, ((1,),))) == 8
    assert count_bruteforce(CNFFormula(3, ((1, -1),))) == 8
    assert CNFFormula(3, ((2, 2, -1), (2, -1, 2), (2, -1, 3))).clauses == ((-1, 2),)
    assert CNFFormula(3, ((), (1,), (-2,))).clauses == ((),)


def test_exhaustive_small_clause_subsets_against_independent_specification() -> None:
    possible = ((), (1,), (-1,), (2,), (-2,), (1, 2), (1, -2), (-1, 2), (-1, -2))
    for presence in product((False, True), repeat=len(possible)):
        clauses = tuple(c for c, present in zip(possible, presence) if present)
        assert count_bruteforce(CNFFormula(2, clauses)) == independent_count(2, clauses)
    for clauses in (
        ((1, 1, -1),), ((1, 1),), ((1, -1, 2), (2,)),
        ((1, 1, 2), (-1, -1, -2)), ((-1, 2), (-1, 2, 3)),
    ):
        assert count_bruteforce(CNFFormula(3, clauses)) == independent_count(3, clauses)


def test_random_cnf_counts_up_to_twelve_variables() -> None:
    rng = Random(20261025)
    for nvars in range(1, 13):
        for _ in range(18):
            clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randrange(1, nvars + 1)
                                  for _ in range(rng.randrange(0, 5)))
                            for _ in range(rng.randrange(0, 13)))
            expected = independent_count(nvars, clauses)
            assert count_bruteforce(CNFFormula(nvars, clauses), max_variables=12,
                                    max_assignments=1 << 12) == expected


def test_dimacs_roundtrip_comments_and_multiline_clauses() -> None:
    original = CNFFormula.from_dimacs('c heading\np cnf 4 4\n1 -2\nc comment\n3 0\n2 2 0\n4 -4 0\n-1 0\n')
    assert original.nvars == 4
    assert original == CNFFormula.from_dimacs(original.to_dimacs())
    assert original == CNFFormula(4, ((1, -2, 3), (2,), (4, -4), (-1,)))
    assert CNFFormula.from_dimacs('p cnf 0 0\n') == CNFFormula(0, ())
    assert CNFFormula.from_dimacs('p cnf 2 1\n0\n') == CNFFormula(2, ((),))


@pytest.mark.parametrize('text', [
    '', 'c only comments', 'p cfn 1 0', 'p cnf 1 -1', 'p cnf 1 1\n1',
    'p cnf 1 1\n2 0', 'p cnf 1 1\na 0', 'p cnf 1 0\n0',
    'p cnf 1 1\n1 0 0', 'p cnf 1 2\n1 0',
])
def test_dimacs_rejects_invalid_or_incomplete_input(text: str) -> None:
    with pytest.raises(ValueError):
        CNFFormula.from_dimacs(text)


@pytest.mark.parametrize('nvars, clauses', [
    (-1, ()), (True, ()), (1, ((0,),)), (1, ((2,),)), (1, ((True,),)),
    (2, ((1.0,),)), (0, ((-1,),)),
])
def test_rejects_invalid_cnf(nvars: int, clauses: tuple[tuple[int, ...], ...]) -> None:
    with pytest.raises(ValueError):
        CNFFormula(nvars, clauses)


def test_capacity_is_explicit_even_for_trivial_formulas() -> None:
    with pytest.raises(CapacityError):
        count_bruteforce(CNFFormula(12, ()), max_variables=11)
    with pytest.raises(CapacityError):
        count_bruteforce(CNFFormula(12, ((),)), max_assignments=100)
    with pytest.raises(ValueError):
        count_bruteforce(CNFFormula(1, ()), max_assignments=0)
    with pytest.raises(ValueError):
        CNFFormula(2, ()).satisfied_mask(4)


def test_unique_auxiliary_extensions_survive_sudoku_adapter() -> None:
    f = CNF()
    x, y = f.var(), f.var()
    z = f.or_gate(x, y)
    adapted = from_sudoku_cnf(f)
    assert adapted.nvars == 3
    assert count_bruteforce(adapted) == 4
    for vx, vy in product((False, True), repeat=2):
        bits = f.extend({x: vx, y: vy})
        assert bits[z] == (vx or vy)
        mask = sum(int(value) << (index - 1) for index, value in enumerate(bits) if index)
        assert adapted.satisfied_mask(mask)
        wrong = mask ^ (1 << (z - 1))
        assert not adapted.satisfied_mask(wrong)


def test_sudoku_puzzle_adapter_preserves_declared_variables_and_witness() -> None:
    puzzle = Puzzle.from_text('1', b=1)
    formula = from_sudoku_puzzle(puzzle)
    assert formula.nvars == 1
    assert count_bruteforce(formula) == 1
    puzzle2 = Puzzle.from_text('1234341221434321', b=2)
    cnf = puzzle2.encode()
    adapted = from_sudoku_cnf(cnf)
    witness = puzzle2.witness(cnf, puzzle2.entries)
    assignment = sum(int(value) << (index - 1) for index, value in enumerate(witness) if index)
    assert adapted.satisfied_mask(assignment)
