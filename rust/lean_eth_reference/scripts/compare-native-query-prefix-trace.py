#!/usr/bin/env python3
"""Strict source-IMPORTED Lean vs Rust query-prefix physical trace comparison.

The Lean output MUST be produced by the original pinned OpenAI source and
cannot be synthesized or substituted with the Rust output. This comparator
performs format, completeness, and exact-cell comparisons only.
"""
from __future__ import annotations

import argparse
from pathlib import Path

EXPECTED = frozenset({"empty", "none", "first", "middle", "separated", "all"})


def parse(path: Path) -> dict[str, tuple[str, ...]]:
    rows = {}
    for lineno, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip():
            continue
        fields = line.strip().split("|")
        if len(fields) != 15 or fields[0] != "prepare":
            raise ValueError(f"{path}:{lineno}: malformed query-prefix record")
        case = fields[1]
        if case not in EXPECTED or case in rows:
            raise ValueError(f"{path}:{lineno}: unknown or duplicate fixture {case}")
        if not fields[2].isdecimal() or int(fields[2]) < 1:
            raise ValueError(f"{path}:{lineno}: invalid physical step count")
        if any(set(bits) - {"0", "1"} for bits in fields[3:]):
            raise ValueError(f"{path}:{lineno}: invalid Boolean stack or register")
        if len(fields[14]) != 1:
            raise ValueError(f"{path}:{lineno}: invalid guard register")
        rows[case] = tuple(fields[2:])
    if set(rows) != EXPECTED:
        raise ValueError(f"{path}: missing {sorted(EXPECTED - rows.keys())}")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--rust", type=Path, required=True)
    args = parser.parse_args()
    if args.lean.resolve() == args.rust.resolve():
        raise ValueError("Lean and Rust source paths must differ")
    lean = parse(args.lean)
    rust = parse(args.rust)
    for case in sorted(EXPECTED):
        if lean[case] != rust[case]:
            raise AssertionError(f"{case}: Lean/Rust divergence: Lean {lean[case]}, Rust {rust[case]}")
    print(f"Matched {len(EXPECTED)} imported-source Lean/Rust query-prefix machine traces")


if __name__ == "__main__":
    main()
