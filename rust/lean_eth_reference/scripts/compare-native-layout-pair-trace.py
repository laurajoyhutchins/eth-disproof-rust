#!/usr/bin/env python3
"""Strictly compare independent imported-source Lean and Rust machine traces.

Requires actual source-executed Lean output. Never fabricate a Lean result from
Rust output: a self-comparison is NOT cross-language conformance.
"""
from __future__ import annotations
import argparse
from pathlib import Path

EXPECTED = {(kind, str(i)) for kind in ('layout', 'pair') for i in range(4)}


def parse(path: Path) -> dict[tuple[str, str], tuple[str, ...]]:
    result = {}
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
        if not raw.strip():
            continue
        fields = raw.split('|')
        key = tuple(fields[:2])
        width = {'layout': 10, 'pair': 12}.get(fields[0])
        if width is None or len(fields) != width or key not in EXPECTED or key in result:
            raise ValueError(f'{path}:{lineno}: malformed or duplicate trace row')
        if not fields[2].isdecimal() or int(fields[2]) == 0:
            raise ValueError(f'{path}:{lineno}: missing source instruction count')
        for index, field in enumerate(fields[3:], 3):
            if set(field) - {'0', '1', ','}:
                raise ValueError(f'{path}:{lineno}: invalid binary word at {index}')
        if len(fields[-1]) != 1 or len(fields[-2]) != 1:
            raise ValueError(f'{path}:{lineno}: malformed final register flags')
        if fields[0] == 'layout' and (len(fields[3].split(',')) != 14 or len(fields[4].split(',')) != 14):
            raise ValueError(f'{path}:{lineno}: missing master word')
        if fields[0] == 'pair' and len(fields[7].split(',')) != 5:
            raise ValueError(f'{path}:{lineno}: missing pair scratch bank')
        result[key] = tuple(fields[2:])
    if set(result) != EXPECTED:
        raise ValueError(f'{path}: missing {sorted(EXPECTED - set(result))}')
    return result


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', required=True, type=Path)
    ap.add_argument('--rust', required=True, type=Path)
    args = ap.parse_args()
    if args.lean.resolve() == args.rust.resolve():
        raise ValueError('Lean and Rust inputs must be distinct files')
    lean = parse(args.lean)
    rust = parse(args.rust)
    for key in sorted(EXPECTED):
        if lean[key] != rust[key]:
            raise AssertionError(f'{key}: original Lean and Rust machine traces diverge')
    print('PASS: eight imported-source Lean vs Rust layout and pair traces')


if __name__ == '__main__':
    main()
