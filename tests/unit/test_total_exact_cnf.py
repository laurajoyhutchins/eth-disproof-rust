"""Constructive whole-kernel bit and storage tests for a total exponential baseline.

The mathematically complete kernel is intentionally different from the
partial paper solver. These tests verify the source's accounted events
and arithmetic envelopes, not a non-exponential result.
"""
from __future__ import annotations

from itertools import combinations
from random import Random

import pytest

from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
from reference.total_exact_cnf import (
    count_total_reference, total_reference_envelope,
)


@pytest.mark.checkpoint
@pytest.mark.parametrize(("n", "clauses", "expected"), [
    (0, (), 1),
    (0, ((),), 0),
    (1, (), 2),
    (1, ((1,),), 1),
    (1, ((-1,),), 1),
    (1, ((1,), (-1,)), 0),
    (2, ((1, 2),), 3),
    (3, ((1, -2), (2, 3)), 4),
    (4, ((1, -1),), 16),
    (4, ((1, 2), (1, 2)), 12),
    (6, ((1, 3), (3, 5), (1, 5)), 32),
])
def test_total_reference_count_and_bit_envelope(
    n: int, clauses: tuple[tuple[int, ...], ...], expected: int,
) -> None:
    formula = CNFFormula(n, clauses)
    result = count_total_reference(formula)
    assert result.count == count_bruteforce(formula) == expected
    stats = result.stats
    assert stats.factor_eliminations == n
    assert stats.maximum_integer_bits <= n + 1
    assert stats.operand_aware_bit_steps > 0
    assert stats.operand_aware_bit_steps.bit_length() <= stats.log2_work_upper
    assert stats.peak_modelled_bit_cells.bit_length() <= stats.log2_storage_upper
    assert stats.peak_live_table_entries <= (
        len(formula.clauses) + n + 2
    ) * (1 << n)


@pytest.mark.integration
def test_exhaustively_small_normalized_cnfs_with_independent_oracle() -> None:
    """All combinations up to three clauses over a controlled 3-var catalog."""
    candidates = (
        (), (1,), (-1,), (2,), (-2,), (3,), (-3,),
        (1, 2), (1, -2), (-1, 2), (-1, -2),
        (1, 3), (2, 3), (-2, 3), (2, -3),
    )
    checked = 0
    for count in range(4):
        for clauses in combinations(candidates, count):
            formula = CNFFormula(3, clauses)
            actual = count_total_reference(formula)
            assert actual.count == count_bruteforce(formula)
            assert actual.stats.maximum_integer_bits <= 4
            assert actual.stats.operand_aware_bit_steps.bit_length() <= (
                actual.stats.log2_work_upper
            )
            assert actual.stats.peak_modelled_bit_cells.bit_length() <= (
                actual.stats.log2_storage_upper
            )
            checked += 1
    assert checked == 576


@pytest.mark.integration
def test_random_low_width_instances_and_adversarial_dense_boundaries() -> None:
    rng = Random(22739)
    for n in range(1, 9):
        for _ in range(12):
            clauses = []
            for _ in range(n + 3):
                width = rng.randrange(min(3, n) + 1)
                variables = rng.sample(range(1, n + 1), width)
                clauses.append(tuple(v if rng.randrange(2) else -v
                                     for v in variables))
            formula = CNFFormula(n, tuple(clauses))
            result = count_total_reference(formula)
            assert result.count == count_bruteforce(formula)
            assert result.stats.maximum_integer_bits <= n + 1
            assert result.stats.operand_aware_bit_steps.bit_length() <= (
                result.stats.log2_work_upper
            )
            assert result.stats.peak_modelled_bit_cells.bit_length() <= (
                result.stats.log2_storage_upper
            )


@pytest.mark.checkpoint
def test_symbolic_envelope_never_enumerates_enormous_cube() -> None:
    n = 10**100
    bound = total_reference_envelope(n, n * 3, 3)
    assert bound.log2_work_upper > n
    assert bound.log2_work_upper < n + 10_000
    assert bound.log2_storage_upper > n
    assert bound.address_bits >= n
    with pytest.raises(ValueError):
        total_reference_envelope(4, 2, 5)
    with pytest.raises(ValueError):
        total_reference_envelope(-1, 0, 0)


@pytest.mark.checkpoint
def test_total_exponential_reference_does_not_discharge_sudoku_theorem() -> None:
    from reference.complete_theorem_gate import (
        IncompleteTheorem, current_theorem_status,
    )

    # A complete cost proof for a different exponential algorithm cannot
    # be substituted into the conditional paper recurrence.
    envelope = total_reference_envelope(6, 8, 3)
    assert envelope.log2_work_upper >= 6
    with pytest.raises(IncompleteTheorem, match="source_or_totality"):
        current_theorem_status(local_bit_work_gap=None).require_complete()
