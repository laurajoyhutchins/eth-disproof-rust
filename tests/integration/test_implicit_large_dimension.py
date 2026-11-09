"""Large virtual auxiliary dimension: an exact small-CNF integration witness.

The coordinate count is intentionally huge but the actual CNF has just three
variables.  This proves the implicit representation is executable without a
dense D**2 matrix; it is NOT a worst-case subexponential speed claim.
"""
from __future__ import annotations

import pytest

from non_exponential_sudoku.eth import (
    CNFFormula, construct_implicit_auxiliary, construct_from_schedules,
    count_bruteforce, count_from_constructed, deterministic_schedules,
)

pytestmark = pytest.mark.integration


@pytest.mark.parametrize("Q", [5, 12])
def test_count_without_materializing_virtual_auxiliary_space(Q: int) -> None:
    formula = CNFFormula(3, ((1, 2), (-1, 3)))
    auxiliary = construct_implicit_auxiliary(r=2, Q=Q, R=Q)
    assert auxiliary.dimension == 4 ** Q
    assert len(auxiliary.measurement_selectors) == 1
    variables, clauses = deterministic_schedules(formula, r=2, Q=Q)
    constructed = construct_from_schedules(formula, auxiliary, variables, clauses)
    assert len(constructed.centers) == Q
    assert count_from_constructed(formula, constructed) == count_bruteforce(formula) == 4
