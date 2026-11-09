"""Fast, independent fixture tests for the optional real-Lean trace comparator."""
from __future__ import annotations

import pytest

from scripts.compare_lean_trace import compare, expected, parse_trace


@pytest.mark.checkpoint
def test_source_trace_fixture_contract() -> None:
    pairs = expected()
    assert len(pairs) == 16
    assert all(set(value) <= {'0', '1'} for value in pairs.values())
    fixture = '\n'.join(f"{name}|{bits}" for name, bits in pairs.items())
    compare(fixture)


@pytest.mark.integration
def test_trace_comparison_rejects_semantic_mismatch() -> None:
    pairs = expected()
    changed = {**pairs, 'branchA': pairs['branchB']}
    fixture = '\n'.join(f"{name}|{bits}" for name, bits in changed.items())
    with pytest.raises(AssertionError, match='branchA mismatch'):
        compare(fixture)


@pytest.mark.integration
def test_trace_parser_refuses_missing_and_duplicate_records() -> None:
    with pytest.raises(ValueError, match='duplicate'):
        parse_trace('case|1\ncase|0\n')
    with pytest.raises(ValueError, match='unexpected'):
        parse_trace('not a record')
    with pytest.raises(AssertionError, match='trace keys differ'):
        compare('empty0|00\n')


@pytest.mark.checkpoint
def test_counting_dfs_cannot_use_satisfiability_only_leaf_overlap() -> None:
    from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
    from non_exponential_sudoku.eth.sparsification import _children

    formula = CNFFormula(3, ((1, 2), (1, 3)))
    count_a, count_b = _children(formula, 2, (1,))
    assert count_bruteforce(formula) == 5
    assert count_bruteforce(count_a) + count_bruteforce(count_b) == 5
    # ExecSparsifyWorklist (SAT-only) instead uses (x2 AND x3) on B;
    # that has overlapping models and would overcount if treated as #SAT.
    satisfiability_only_b = CNFFormula(3, ((2,), (3,)))
    assert count_bruteforce(count_a) + count_bruteforce(satisfiability_only_b) == 6
