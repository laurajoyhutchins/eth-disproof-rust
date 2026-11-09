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


def test_count_with_huge_global_exceptional_subspace() -> None:
    """Q=6R, no retained eigenvectors: exact 3-CNF readout still works.

    This is a full computation at virtual auxiliary dimension 4**48,
    but the Boolean input has only three variables. It establishes
    representational feasibility, not the paper's worst-case bound.
    """
    formula = CNFFormula(3, ((1, 2), (-1, 3)))
    auxiliary = construct_implicit_auxiliary(
        r=2, Q=48, R=8, measurement_basis='projector')
    assert auxiliary.dimension == 4 ** 48
    assert auxiliary.exceptional_count > 10 ** 28
    assert auxiliary.measurement_selectors == ()
    a, d = deterministic_schedules(formula, r=2, Q=48)
    design = construct_from_schedules(formula, auxiliary, a, d)
    assert len(design.centers) == 48
    assert design.max_measurement_rows == 3
    assert all(sum(abs(value) for value in row) <= 1
               for _, center in design.centers for matrix in center.matrices
               for row in matrix)
    assert count_from_constructed(formula, design) == count_bruteforce(formula) == 4


def test_restricted_projector_rank_obstruction() -> None:
    """Observed full restricted rank is a *lower bound* on measurement rows."""
    from benchmarks.eth.projector_probe import rank_audit

    evidence = rank_audit()
    assert [item['nvars'] for item in evidence] == [4, 8, 16, 24]
    for item in evidence:
        n = item['nvars']
        assert item['min_rank'] == item['max_rank'] == n
        assert item['max_row_l1'] == 1
        assert item['observed_tau'] == '1/2'


def test_factorized_taylor_scales_to_sixty_four_variable_chain() -> None:
    """Finite-size exact factorized count, not arbitrary-CNF #SAT scaling."""
    from non_exponential_sudoku.eth.interpolation import count_origin_from_manual_designs
    from non_exponential_sudoku.eth.taylor import TaylorLimits

    n = 64
    formula = CNFFormula(n, tuple((2 * i + 1, 2 * i + 3)
                                  for i in range(n // 2 - 1)))
    groups = tuple((i, i + 1) for i in range(0, n, 2))
    design = MeasurementDesign(
        groups=groups, clause_groups=tuple(range(len(formula.clauses))),
        matrices=tuple(((1, 0), (0, 1)) for _ in groups),
        tau=Fraction(1, 2), D=1,
    )
    counted = count_origin_from_manual_designs(
        formula, ((Fraction(1), design),), order=0,
        summation='eliminate',
        taylor_limits=TaylorLimits(max_measurement_tuples=1, max_factor_entries=128),
    )
    assert counted.count == 24_493_713_157_783_552
    stats = counted.taylor_data[0].stats
    assert stats.factor_scope_peak == 2
    assert stats.factor_entries_peak <= 12
    assert stats.factor_assignments_tested == 996
    assert stats.measurement_tuples == 0
