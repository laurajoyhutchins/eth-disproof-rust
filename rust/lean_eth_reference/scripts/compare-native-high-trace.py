#!/usr/bin/env python3
"""Fail-closed comparison of REAL source-executed Lean and Rust trace lines.

Lean file: reference/lean_native_high_trace.lean. The comparator does not generate substitute Lean traces. Only pass an output
from the actual source-importing Lean entrypoint as --lean.
"""
from __future__ import annotations

import argparse
from pathlib import Path

CASES = {"empty", "zero", "one", "mixed", "alternate", "all"}
KINDS = {"branch", "initialize"}


def parse(path: Path) -> dict[tuple[str, str], tuple[str, ...]]:
    rows: dict[tuple[str, str], tuple[str, ...]] = {}
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        parts = line.split("|")
        if len(parts) != 7:
            raise ValueError(f"{path}:{lineno}: expected seven fields")
        kind, case, steps, *remaining = parts
        if kind not in KINDS or case not in CASES or not steps.isdecimal():
            raise ValueError(f"{path}:{lineno}: invalid case / step count")
        if any(any(char not in "01" for char in value) for value in remaining):
            raise ValueError(f"{path}:{lineno}: non-binary word")
        if any(len(word) != 1 for word in remaining[-(2 if kind == 'branch' else 1):]):
            raise ValueError(f"{path}:{lineno}: invalid Boolean register")
        key = (kind, case)
        if key in rows:
            raise ValueError(f"{path}:{lineno}: duplicate {key}")
        rows[key] = tuple(parts[2:])
    expected = {(kind, case) for kind in KINDS for case in CASES}
    if rows.keys() != expected:
        raise ValueError(f"{path}: missing {expected - rows.keys()}, extra {rows.keys() - expected}")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--rust", type=Path, required=True)
    args = parser.parse_args()
    if args.lean.resolve() == args.rust.resolve():
        raise ValueError("Lean and Rust inputs must be distinct files")
    left, right = parse(args.lean), parse(args.rust)
    for key, value in left.items():
        if right[key] != value:
            raise AssertionError(f"source Lean/Rust {key} mismatch: Lean={value}, Rust={right[key]}")
    print(f"trace streams agree on {len(left)} complete machine traces (provenance not independently checked)")


if __name__ == "__main__":
    main()
