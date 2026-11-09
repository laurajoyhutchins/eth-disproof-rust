"""Differential proof fixtures for exact tensor bond-rank growth.

The matching cut is deliberately a bad ordering. Pair-interleaved order
has max rank 2 and no exponential difficulty. The tests distinguish
tensor representation complexity from #SAT decision/counting hardness.
"""
from __future__ import annotations

import pytest

from benchmarks.eth.tensor_bond_obstruction import matching_case
from non_exponential_sudoku.eth.cnf import count_bruteforce
from non_exponential_sudoku.eth.tensor_train import (
    TensorLimits, contract_certified_order_zero,
)
from non_exponential_sudoku.runtime.budget import CapacityError


@pytest.mark.integration
@pytest.mark.parametrize('k', [1, 2, 3, 4])
def test_exact_matching_tensor_bonds_vs_paired_order(k: int) -> None:
    for paired in (False, True):
        formula, design = matching_case(k, interleaved=paired)
        result = contract_certified_order_zero(
            formula, design, at=1,
            limits=TensorLimits(max_bond=512, max_rational_operations=6_000_000),
        )
        assert result.value == count_bruteforce(formula) == 3 ** k
        assert max(result.stats.final_bonds, default=1) == (
            2 if paired else 1 << k)
        assert result.stats.maximum_clause_width == 2
        assert result.stats.theoretical_clause_bond_bound == 5
        if not paired:
            assert result.stats.final_bonds[k - 1] == 1 << k


@pytest.mark.integration
def test_exact_rank_budget_refuses_bad_group_order_without_guessing() -> None:
    formula, design = matching_case(4, interleaved=False)
    with pytest.raises(CapacityError, match='bond'):
        contract_certified_order_zero(
            formula, design, at=1,
            limits=TensorLimits(max_bond=5, max_rational_operations=6_000_000),
        )
