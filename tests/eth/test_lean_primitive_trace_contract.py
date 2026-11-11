"""Checkpoint-fast schema checks for opt-in native BitProgram execution."""
from __future__ import annotations

import pytest

from scripts.compare_lean_primitive import compare, expected, parse


@pytest.mark.checkpoint
def test_primitive_trace_contract_happy_path() -> None:
    wanted = expected()
    fixture = '\n'.join(
        f'{name}.{suffix}|{value}'
        for name, (input_word, output_word) in wanted.items()
        for suffix, value in (
            ('input', input_word), ('output', output_word),
            ('steps', '25'), ('peak', str(len(output_word) + 1)),
            ('pcAfter1', '42'), ('halted', '1'), ('ready', '1'))
    )
    assert compare(fixture) == {name: 25 for name in wanted}


@pytest.mark.checkpoint
def test_primitive_trace_rejects_truncated_or_corrupted_observations() -> None:
    with pytest.raises(ValueError, match='duplicate'):
        parse('same.input|0\nsame.input|1\n')
    with pytest.raises(AssertionError, match='schema mismatch'):
        compare('norm.empty3.input|0\n')

    wanted = expected()
    fixture = '\n'.join(
        f'{name}.{suffix}|{value}'
        for name, (input_word, output_word) in wanted.items()
        for suffix, value in (
            ('input', input_word), ('output', output_word),
            ('steps', '25'), ('peak', str(len(output_word) + 1)),
            ('pcAfter1', '42'), ('halted', '1'), ('ready', '1'))
    )
    with pytest.raises(AssertionError, match='norm.raw3.output'):
        compare(fixture.replace('norm.raw3.output|', 'norm.raw3.output|1', 1))
    with pytest.raises(AssertionError, match='leaf.empty3.ready'):
        compare(fixture.replace('leaf.empty3.ready|1', 'leaf.empty3.ready|0'))
