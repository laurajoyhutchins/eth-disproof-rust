"""Count-preserving up to an explicit power-of-two free-variable factor."""
from __future__ import annotations

from random import Random
from importlib.util import find_spec

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, audit_bounded_cnf, count_bruteforce,
    count_ganak, prepare_bounded_cnf, project_free_variables,
)
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def test_projection_reindexes_without_implicit_existence_quantifier() -> None:
    f = CNFFormula(8, ((-3, 8), (3, 5), (5,)))
    p = project_free_variables(f)
    assert p.old_variables == (3, 5, 8)
    assert p.free_bits == 5
    assert p.formula == CNFFormula(3, ((-1, 3), (1, 2), (2,)))
    assert p.restore_count(count_bruteforce(p.formula)) == count_bruteforce(f)


def test_projection_handles_tautologies_empty_and_zero_counts() -> None:
    for f in (CNFFormula(9, ()), CNFFormula(9, ((1, -1),)),
              CNFFormula(9, ((),)), CNFFormula(0, ()), CNFFormula(0, ((),))):
        p = project_free_variables(f)
        assert p.old_variables == ()
        assert p.restore_count(count_bruteforce(p.formula)) == count_bruteforce(f)
    p = project_free_variables(CNFFormula(1_000_000_000, ()))
    assert p.free_bits == 1_000_000_000
    with pytest.raises(CapacityError, match='bit limit'):
        p.restore_count(1)
    assert p.restore_count(0) == 0
    with pytest.raises(ValueError):
        p.restore_count(-1)
    with pytest.raises(ValueError):
        p.restore_count(1, max_output_bits=0)


def test_prepared_reduction_counts_match_reference_and_ganak() -> None:
    rng = Random(20261108)
    for _ in range(75):
        n = rng.randint(0, 8)
        clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randint(0, 5)))
                        for _ in range(rng.randint(0, 5))) if n else ((),)
        f = CNFFormula(n, clauses)
        prepared = prepare_bounded_cnf(f)
        assert all(len(c) <= 3 for c in prepared.formula.clauses)
        occurrences = [0] * prepared.formula.nvars
        for clause in prepared.formula.clauses:
            for lit in clause:
                occurrences[abs(lit) - 1] += 1
        assert max(occurrences, default=0) <= 3
        # No variable is left free by the parsimonious transform.
        assert all(occurrences) or prepared.formula.nvars == 0
        expected = count_bruteforce(f)
        if find_spec("pyganak") is not None:
            assert prepared.restore_count(count_ganak(prepared.formula)) == expected
        if prepared.formula.nvars <= 15:
            assert prepared.restore_count(count_bruteforce(
                prepared.formula, max_variables=15, max_assignments=1 << 15)) == expected
        audit = audit_bounded_cnf(prepared.formula)
        assert dict(audit.conditions)['three_occurrences_and_width_three']


def test_free_projection_uses_normalized_formula_semantics() -> None:
    # Clause elimination can produce newly unused variables without changing
    # declared-variable counts. The factor must include all of them.
    f = CNFFormula(6, ((1,), (1, 2), (1, 2, 3), (-4, 5)))
    p = project_free_variables(f)
    assert p.old_variables == (1, 4, 5)
    assert p.free_bits == 3
    assert p.restore_count(count_bruteforce(p.formula)) == count_bruteforce(f)
