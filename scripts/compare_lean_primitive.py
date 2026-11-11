"""Validate direct Lean BitProgram primitive instruction runs.

Requires the captured output of reference/lean_primitive_trace.lean, which
imports and executes unmodified pinned OpenAI source. Only bounded finite
normalization and terminal counting are covered. No primitive VM was ported
to Python; checking semantic outputs is not instruction-level equivalence.
"""
from __future__ import annotations

import argparse
from pathlib import Path

from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.lean_wire import (
    _encode_list, _encode_nat, encode_lean_cnf,
)


def bits(word: tuple[bool, ...]) -> str:
    return ''.join('1' if bit else '0' for bit in word)


def raw_body(nvars: int, clauses: tuple[tuple[int, ...], ...]) -> tuple[bool, ...]:
    """Lean's raw finite *set* encoding before SAT.normalize."""
    numbers = sorted({
        tuple(sorted(2 * (abs(lit) - 1) + int(lit > 0)
                     for lit in clause))
        for clause in clauses
    })
    assert all(0 <= code < 2 * nvars for row in numbers for code in row)
    return _encode_list(numbers, lambda row: _encode_list(row, _encode_nat))


def expected() -> dict[str, tuple[str, str]]:
    normalized = {
        'norm.empty3': (CNFFormula(3, ()), ()),
        'norm.false3': (CNFFormula(3, ((),)), ((),)),
        'norm.raw3': (CNFFormula(3, ((1, -1), (1, 2), (1,))),
                      ((1, -1), (1, 2), (1,))),
    }
    result = {
        name: (
            bits(raw_body(formula.nvars, raw)),
            bits(encode_lean_cnf(formula)[formula.nvars + 1:]),
        )
        for name, (formula, raw) in normalized.items()
    }
    result['leaf.empty3'] = (
        bits(_encode_list((), lambda row: tuple(row))), '0001',
    )
    result['leaf.false3'] = (
        bits(_encode_list(((False,),), lambda row: tuple(row))), '0',
    )
    return result


def parse(source: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in source.splitlines():
        if not line.strip():
            continue
        if '|' not in line:
            raise ValueError(f'unexpected Lean output: {line!r}')
        key, value = line.strip().split('|', 1)
        if not key or key in result:
            raise ValueError(f'duplicate or empty Lean key: {key!r}')
        result[key] = value
    return result


def compare(source: str) -> dict[str, int]:
    observed = parse(source)
    wanted = expected()
    expected_keys = {
        f'{name}.{suffix}' for name in wanted
        for suffix in ('input', 'output', 'steps', 'peak',
                       'pcAfter1', 'halted', 'ready')
    }
    if observed.keys() != expected_keys:
        raise AssertionError(
            f'trace schema mismatch missing={sorted(expected_keys - observed.keys())}'
            f' extra={sorted(observed.keys() - expected_keys)}'
        )
    counts: dict[str, int] = {}
    for name, (input_word, output_word) in wanted.items():
        for suffix, expected_word in (('input', input_word), ('output', output_word),
                                      ('halted', '1'), ('ready', '1')):
            actual = observed[f'{name}.{suffix}']
            if actual != expected_word:
                raise AssertionError(
                    f'{name}.{suffix}: Lean={actual!r} Python={expected_word!r}'
                )
        steps = int(observed[f'{name}.steps'])
        peak = int(observed[f'{name}.peak'])
        first_pc = int(observed[f'{name}.pcAfter1'])
        if not 0 < steps <= 250000:
            raise AssertionError(f'{name}: invalid primitive steps {steps}')
        if peak < len(output_word) or first_pc < 0:
            raise AssertionError(f'{name}: invalid primitive state/stack evidence')
        counts[name] = steps
    print('Pinned Lean BitProgram: 5 physical runs verified; '
          f'primitive steps: {counts}')
    return counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    args = parser.parse_args()
    compare(args.input.read_text())


if __name__ == '__main__':
    main()
