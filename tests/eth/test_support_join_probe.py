"""TDD: structural and adversarial exact factor-join experiment."""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations

import pytest

from benchmarks.eth.support_join_probe import (
    CapacityRefusal,
    brute_count,
    make_family,
    run_contraction,
)


@pytest.mark.integration
@pytest.mark.parametrize('family, sizes', [
    ('chain', (2, 3, 4, 6, 8)),
    ('equality-clique', (2, 3, 4, 6, 8)),
    ('or-clique', (2, 3, 4, 6, 8)),
])
def test_dense_and_support_join_match_independent_enumeration(family, sizes):
    for n in sizes:
        factors = make_family(family, n)
        oracle = brute_count(n, factors)
        dense = run_contraction(n, factors, strategy='dense')
        support = run_contraction(n, factors, strategy='support')
        assert dense.answer == support.answer == oracle
        assert dense.steps[-1].output_entries == support.steps[-1].output_entries == 1


@pytest.mark.integration
def test_family_counts_have_independent_closed_forms():
    for n in range(2, 9):
        chain = brute_count(n, make_family('chain', n))
        a, b = 0, 1
        for _ in range(n + 2):
            a, b = b, a + b
        assert chain == a
        assert brute_count(n, make_family('equality-clique', n)) == 2
        assert brute_count(n, make_family('or-clique', n)) == n + 1


@pytest.mark.integration
def test_equality_clique_support_growth_is_not_dense_cartesian_growth():
    for n in (4, 6, 8, 10):
        factors = make_family('equality-clique', n)
        dense = run_contraction(n, factors, strategy='dense')
        support = run_contraction(n, factors, strategy='support')
        assert dense.answer == support.answer == 2
        assert dense.steps[0].joined_scope == tuple(range(n))
        assert dense.steps[0].dense_domain == 1 << n
        assert support.steps[0].joined_scope == dense.steps[0].joined_scope
        # The peak includes all still-live original factors and temporary
        # joins, so only the induced *output support* is compared to 2**n.
        assert support.steps[0].output_entries == 2
        assert support.steps[0].output_entries < (1 << n)
        assert support.candidate_pairs < dense.candidate_assignments * n * n


@pytest.mark.integration
def test_or_clique_retains_exponential_intermediate_support():
    for n in (4, 6, 8):
        support = run_contraction(n, make_family('or-clique', n), strategy='support')
        assert support.answer == n + 1
        # After eliminating x0, f(y)=1+product(y_i), which is nonzero for
        # every assignment to the other n-1 variables. This table is dense.
        assert support.steps[0].output_entries == 1 << (n - 1)
        assert support.steps[0].output_bits <= n.bit_length() + 1


@pytest.mark.checkpoint
def test_small_capacity_refuses_without_silent_fallback():
    with pytest.raises(CapacityRefusal):
        run_contraction(8, make_family('or-clique', 8), strategy='support', max_entries=16)
    with pytest.raises(CapacityRefusal):
        run_contraction(8, make_family('equality-clique', 8), strategy='dense', max_candidates=100)


@pytest.mark.checkpoint
def test_invalid_factors_refused():
    with pytest.raises(ValueError):
        make_family('chain', 1)
    with pytest.raises(ValueError):
        run_contraction(3, make_family('chain', 3), strategy='unknown')


@pytest.mark.integration
@pytest.mark.parametrize('n', (4, 6))
def test_actual_certified_taylor_paths_have_same_or_clique_width(n: int) -> None:
    """Connect the isolated order-zero obstruction to the current ETH evaluator."""
    from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
    from non_exponential_sudoku.eth.design import MeasurementDesign
    from non_exponential_sudoku.eth.taylor import taylor_coefficients_separated

    edges = tuple(combinations(range(n), 2))
    formula = CNFFormula(n, tuple((i + 1, j + 1) for i, j in edges))
    design = MeasurementDesign(
        groups=tuple((i,) for i in range(n)),
        clause_groups=tuple(i for i, _ in edges),
        matrices=tuple(((1,),) for _ in range(n)),
        tau=Fraction(1, 2), D=1,
    )
    expected = count_bruteforce(formula) == n + 1
    assert expected
    for summation in ('eliminate', 'fused'):
        result = taylor_coefficients_separated(
            formula, design, at=Fraction(1), order=0, summation=summation,
        )
        assert result.coefficients == (Fraction(n + 1),)
        assert result.stats.factor_scope_peak == n
        assert result.stats.factor_assignments_tested >= (1 << n)


@pytest.mark.checkpoint
def test_peak_budget_counts_live_bucket_inputs_and_output_together():
    factors = make_family('or-clique', 4)
    initial_entries = sum(len(f.entries) for f in factors)
    # The first bucket's attached input factors are still live while the
    # induced output table is being constructed. Neither can be omitted.
    for strategy in ('dense', 'support'):
        with pytest.raises(CapacityRefusal):
            run_contraction(4, factors, strategy=strategy,
                            max_entries=initial_entries + 1)

