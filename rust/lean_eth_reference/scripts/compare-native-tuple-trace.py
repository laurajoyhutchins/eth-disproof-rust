#!/usr/bin/env python3
"""Strict comparison of source-IMPORTED Lean and Rust physical tuple traces.

This script never creates synthetic Lean output, and explicitly checks the
complete fixture key set before comparing any values. Input provenance is a
caller responsibility; a successful comparison alone is not a formal proof.
"""
from __future__ import annotations

import argparse
from pathlib import Path

ODOMETER = frozenset({"empty", "width0", "one", "two", "split", "three", "carry", "overflow"})
ENUMERATE = frozenset({"empty", "width0", "one", "two", "split", "three"})
EXPECTED = frozenset({("odometer", case) for case in ODOMETER} | {("enumerate", case) for case in ENUMERATE})


def parse(path: Path) -> dict[tuple[str, str], tuple[str, ...]]:
    rows: dict[tuple[str, str], tuple[str, ...]] = {}
    for lineno, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip():
            continue
        columns = line.strip().split("|")
        kind = columns[0]
        length = 8 if kind == "odometer" else 9
        if len(columns) != length:
            raise ValueError(f"{path}:{lineno}: malformed {kind} record")
        key = (kind, columns[1])
        if key not in EXPECTED or key in rows or not columns[2].isdecimal():
            raise ValueError(f"{path}:{lineno}: unexpected, duplicated, or uncounted record {key}")
        words = columns[3:]
        if any(set(word) - {"0", "1"} for word in words):
            raise ValueError(f"{path}:{lineno}: invalid bit word")
        register_count = 3 if kind == "odometer" else 2
        if kind == "odometer" and any(len(word) != 1 for word in words[-register_count:]):
            raise ValueError(f"{path}:{lineno}: malformed Boolean register")
        if kind == "enumerate" and any(len(word) != 1 for word in words[-3:-1]):
            raise ValueError(f"{path}:{lineno}: malformed Boolean register")
        rows[key] = tuple(columns[2:])
    if set(rows) != EXPECTED:
        raise ValueError(f"{path}: missing {sorted(EXPECTED - rows.keys())}; extra {sorted(rows.keys() - EXPECTED)}")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--rust", required=True, type=Path)
    args = parser.parse_args()
    lean = parse(args.lean)
    rust = parse(args.rust)
    for key in sorted(EXPECTED):
        if lean[key] != rust[key]:
            raise AssertionError(f"Lean/Rust {key} differs:\nLean={lean[key]!r}\nRust={rust[key]!r}")
    print(f"Matched all {len(EXPECTED)} physical machine traces (actual-source provenance externally required)")


if __name__ == "__main__":
    main()
