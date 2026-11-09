"""Fast, independent fixture tests for the optional real-Lean trace comparator."""
from __future__ import annotations

import pytest

from scripts.compare_lean_trace import compare, expected, parse_trace


@pytest.mark.checkpoint
def test_source_trace_fixture_contract() -> None:
    pairs = expected()
    assert len(pairs) == 11
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
