#!/usr/bin/env python3
"""Reject any difference in per-instruction PC, complete registers and stacks.

This parser does not run Lean or claim provenance. Its caller MUST produce
Lean output from actual imported upstream definitions at the pinned revision.
"""
from __future__ import annotations

import argparse
from pathlib import Path

EXPECTED = {
    f"{size}_{code}_{mode}"
    for size in range(5)
    for code in range(1 << size)
    for mode in ("clean", "dirty")
}


def parse(path: Path) -> dict[str, list[tuple[str, ...]]]:
    results: dict[str, list[tuple[str, ...]]] = {}
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        columns = line.split("|")
        if len(columns) != 7 or columns[0] != "machine":
            raise ValueError(f"{path}:{number}: expected 7 machine fields")
        _, name, step, pc, regs, left, right = columns
        if name not in EXPECTED:
            raise ValueError(f"{path}:{number}: unexpected test case {name!r}")
        if not step.isascii() or not step.isdecimal():
            raise ValueError(f"{path}:{number}: invalid step count")
        if pc != "H" and (not pc.isascii() or not pc.isdecimal()):
            raise ValueError(f"{path}:{number}: invalid program counter")
        if len(regs) != 2 or any(set(word) - {"0", "1"} for word in (regs, left, right)):
            raise ValueError(f"{path}:{number}: invalid register or stack bits")
        sequence = results.setdefault(name, [])
        if int(step) != len(sequence):
            raise ValueError(f"{path}:{number}: missing/repeated/out-of-order step for {name}")
        if sequence and sequence[-1][1] == "H":
            raise ValueError(f"{path}:{number}: state after halt for {name}")
        sequence.append((step, pc, regs, left, right))
    if set(results) != EXPECTED:
        raise ValueError(f"{path}: missing {sorted(EXPECTED - set(results))}; extra {sorted(set(results) - EXPECTED)}")
    for name, states in results.items():
        if len(states) < 2 or states[-1][1] != "H" or any(s[1] == "H" for s in states[:-1]):
            raise ValueError(f"{path}: missing/early terminal for {name}")
    return results


def compare(left: Path, right: Path) -> tuple[int, int]:
    lean, rust = parse(left), parse(right)
    for name in sorted(EXPECTED):
        for n, (a, b) in enumerate(zip(lean[name], rust[name])):
            if a != b:
                raise AssertionError(f"{name} instruction {n}: source Lean={a}, Rust={b}")
        if len(lean[name]) != len(rust[name]):
            raise AssertionError(f"{name} instruction count Lean={len(lean[name])}, Rust={len(rust[name])}")
    return len(EXPECTED), sum(len(xs) for xs in lean.values())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--rust", type=Path, required=True)
    args = parser.parse_args()
    cases, states = compare(args.lean, args.rust)
    print(f"Matched full machine traces: {cases} cases, {states} states (provenance enforced by caller)")


if __name__ == "__main__":
    main()
