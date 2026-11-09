"""Independent finite-size tests for the OR-clique symmetry quotient."""
from __future__ import annotations

from itertools import product

import pytest

from benchmarks.eth.or_clique_cardinality import (
    count_or_clique_cardinality,
    first_bucket_symbolic_value,
)
from benchmarks.eth.support_join_probe import brute_count, make_family, run_contraction


@pytest.mark.integration
@pytest.mark.parametrize("n", (2, 3, 4, 6, 8, 10))
def test_exact_symmetry_count_matches_independent_oracles(n: int) -> None:
    trace = count_or_clique_cardinality(n)
    factors = make_family("or-clique", n)
    assert trace.count == brute_count(n, factors) == n + 1
    if n <= 8:
        assert trace.count == run_contraction(n, factors, strategy="dense").answer
    assert trace.peak_state_entries == 2
    assert trace.arithmetic_adds == n + 1
    assert trace.max_coefficient_bits <= (n + 1).bit_length()


@pytest.mark.integration
@pytest.mark.parametrize("n", (3, 4, 6, 8))
def test_first_bucket_symbolic_expression_matches_explicit_factor(n: int) -> None:
    factors = make_family("or-clique", n)
    first = run_contraction(n, factors, strategy="dense").steps[0]
    assert first.output_entries == 1 << (n - 1)
    for assignment in product((0, 1), repeat=n - 1):
        direct = sum(
            int(all(x0 or assignment[j - 1] for j in range(1, n)))
            for x0 in (0, 1)
        )
        assert first_bucket_symbolic_value(assignment) == direct


@pytest.mark.checkpoint
def test_cardinality_state_transition_and_refusals() -> None:
    trace = count_or_clique_cardinality(4)
    assert trace.states == ((1, 0), (1, 1), (1, 2), (1, 3), (1, 4))
    assert trace.count == 5
    for invalid in (0, 1, -2, True, 2.5):
        with pytest.raises(ValueError):
            count_or_clique_cardinality(invalid)
    with pytest.raises(ValueError):
        first_bucket_symbolic_value((0, 2))
