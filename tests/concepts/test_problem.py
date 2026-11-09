"""The input object and parsimonious clue semantics are the first contract."""
import pytest
from non_exponential_sudoku.sudoku.three_cnf import Puzzle

pytestmark = pytest.mark.checkpoint


def test_single_cell_has_a_unique_auxiliary_extension() -> None:
    p = Puzzle(1, (1,))
    assert p.valid_solution((1,))
    f = p.encode()
    primary = {f.primary[(0, 0, 1)]: True}
    assert f.satisfied(f.extend(primary))


def test_inconsistent_given_is_not_silently_accepted() -> None:
    p = Puzzle(2, (1, 1) + (0,) * 14)
    assert not p.valid_solution((1,) * 16)
    assert len(p.encode().clauses) > 0
