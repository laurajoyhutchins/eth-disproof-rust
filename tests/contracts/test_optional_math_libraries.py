"""Independent arithmetic and exact-counting contracts for optional libraries."""
from __future__ import annotations

from itertools import product
import random

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.sudoku.three_cnf import CNF, Puzzle
from research.ganak_oracle import count_cnf
from research.flint_oracle import FlintRingOracle

pytestmark = pytest.mark.checkpoint


def _bruteforce(formula: CNF) -> int:
    return sum(formula.satisfied([False, *xs])
               for xs in product((False, True), repeat=formula.nvars))


@pytest.mark.requires_ganak
@pytest.mark.parametrize("nvars,clauses,expected", [
    (0, [], 1), (4, [], 16), (0, [()], 0), (3, [()], 0),
    (3, [(1,)], 4), (3, [(1, 2)], 6), (3, [(1, -1)], 8),
    (2, [(1,), (-1,)], 0), (2, [(1, 2), (-1, 2)], 2),
])
def test_ganak_semantics(nvars: int, clauses: list[tuple[int, ...]], expected: int) -> None:
    pytest.importorskip("pyganak")
    formula = CNF(nvars=nvars, clauses=clauses)
    assert count_cnf(formula) == expected
    assert _bruteforce(formula) == expected


@pytest.mark.requires_ganak
def test_ganak_random_small_formulas() -> None:
    pytest.importorskip("pyganak")
    rng = random.Random(91147)
    for nvars in range(1, 6):
        for _ in range(10):
            clauses = [tuple(rng.choice([-1, 1]) * rng.randint(1, nvars)
                             for _ in range(rng.randint(1, 3)))
                       for _ in range(rng.randint(1, 8))]
            formula = CNF(nvars=nvars, clauses=clauses)
            assert count_cnf(formula) == _bruteforce(formula)


@pytest.mark.requires_ganak
@pytest.mark.parametrize("text,box,expected", [
    (".", 1, 1), ("1", 1, 1),
    ("1234341221434321", 2, 1),
    ("11" + "." * 14, 2, 0),
    ("." * 16, 2, 288),
])
def test_ganak_parsimonious_sudoku_count(text: str, box: int, expected: int) -> None:
    pytest.importorskip("pyganak")
    formula = Puzzle.from_text(text, box).encode()
    assert count_cnf(formula) == expected


def test_ganak_rejects_bad_literals() -> None:
    with pytest.raises(ValueError):
        count_cnf(CNF(nvars=2, clauses=[(3,)]))
    with pytest.raises(ValueError):
        count_cnf(CNF(nvars=2, clauses=[(0,)]))
    with pytest.raises(ValueError):
        count_cnf(CNF(nvars=-1))


@pytest.mark.requires_flint
@pytest.mark.parametrize("degree,precision", [(3, 8), (5, 64), (8, 256)])
def test_flint_composite_quotient_ring(degree: int, precision: int) -> None:
    pytest.importorskip("flint")
    pytest.importorskip("sympy")
    from research.sympy_oracle import SympyRingOracle
    ring = Padic(degree, modulus_polynomial(degree), precision)
    independent = SympyRingOracle(ring)
    flint = FlintRingOracle(ring)
    randomizer = random.Random(degree + precision * 1001)
    magnitude = 1 << precision
    for _ in range(12):
        a = tuple(randomizer.randrange(-magnitude, 2*magnitude) for _ in range(degree))
        b = tuple(randomizer.randrange(-magnitude, 2*magnitude) for _ in range(degree))
        assert flint.add(a, b) == independent.add(a, b)
        assert flint.sub(a, b) == independent.sub(a, b)
        assert flint.mul(a, b) == independent.mul(a, b)
        assert flint.pow(a, 3) == independent.pow(a, 3)
