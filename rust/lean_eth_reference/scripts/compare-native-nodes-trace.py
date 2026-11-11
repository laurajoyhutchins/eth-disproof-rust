#!/usr/bin/env python3
"""Compare original-source Lean and Rust node-cursor machine traces strictly.

The caller MUST supply output from the actual pinned Lean source. Do not
substitute Rust output for Lean output to claim differential conformance.
"""
from __future__ import annotations
import argparse
from pathlib import Path

EXPECTED = frozenset({"empty", "zero", "one", "two", "third", "mixed"})

def parse(path: Path) -> dict[str, tuple[str, ...]]:
    rows: dict[str, tuple[str, ...]] = {}
    for line_no, raw in enumerate(path.read_text().splitlines(), 1):
        if not raw.strip():
            continue
        fields = raw.split("|")
        if len(fields) != 18 or fields[0] != "nodes":
            raise ValueError(f"{path}:{line_no}: invalid node trace format")
        name = fields[1]
        if name not in EXPECTED or name in rows:
            raise ValueError(f"{path}:{line_no}: unknown/duplicate case {name}")
        if any(not count.isdecimal() for count in fields[2:4]):
            raise ValueError(f"{path}:{line_no}: invalid instruction count")
        if int(fields[2]) == 0 or (int(fields[3]) == 0) != (name == "empty"):
            raise ValueError(f"{path}:{line_no}: missing entry/reader execution")
        if any(set(bits) - {"0", "1"} for bits in fields[4:]):
            raise ValueError(f"{path}:{line_no}: invalid physical Boolean value")
        if any(len(bits) != 1 for bits in fields[14:18]):
            raise ValueError(f"{path}:{line_no}: malformed register")
        rows[name] = tuple(fields[2:])
    if set(rows) != EXPECTED:
        raise ValueError(f"{path}: missing {sorted(EXPECTED - rows.keys())}")
    return rows

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean", type=Path, required=True)
    p.add_argument("--rust", type=Path, required=True)
    args = p.parse_args()
    if args.lean.resolve() == args.rust.resolve():
        raise ValueError("Lean and Rust inputs must be separate files")
    lean, rust = parse(args.lean), parse(args.rust)
    for name in sorted(EXPECTED):
        if lean[name] != rust[name]:
            raise AssertionError(f"{name}: original Lean trace and Rust diverged")
    print("Matched 6 imported-source Lean/Rust physical node-cursor traces")

if __name__ == "__main__":
    main()
