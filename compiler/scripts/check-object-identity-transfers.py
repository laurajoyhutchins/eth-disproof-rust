#!/usr/bin/env python3
"""Audit independently observed Lean C/Rust object identities, not pooled counts.

The original Lean source is compiled separately to Lean C and Reader Rust.
Both transcripts must have matching per-run allocation IDs and physical
source-count checkpoints. Passing is finite runtime evidence, not a heap proof.
"""
from __future__ import annotations

import sys
from pathlib import Path


def parse(lines: list[str]) -> dict[str, list[int]]:
    records: dict[str, list[int]] = {}
    for line in lines:
        pieces = line.split()
        if len(pieces) < 3 or pieces[0] != "TRACE":
            raise ValueError("unexpected transcript record")
        name = pieces[1]
        if name in records:
            raise ValueError(f"duplicate transcript checkpoint: {name}")
        numbers = [int(s) for s in pieces[2:]]
        if not all(n >= 0 for n in numbers):
            raise ValueError(f"negative identity or source reference count: {name}")
        records[name] = numbers
    return records


def audit(records: dict[str, list[int]]) -> None:
    expected = {
        "create": 2,
        "direct": 4,
        "second": 2,
        "second-direct": 6,
        "branch-left": 6,
        "branch-right": 6,
        "branch-owners": 8,
        "closure": 4,
        "graph-before": 8,
        "graph-after": 4,
    }
    if set(records) != set(expected):
        raise ValueError(f"missing or extra observable checkpoints: {set(records) ^ set(expected)}")
    for name, size in expected.items():
        if len(records[name]) != size:
            raise ValueError(f"wrong checkpoint field count: {name}")
        if any(n < 1 for n in records[name]):
            raise ValueError(f"invalid heap identity / source count: {name}")
    created = records["create"]
    first = records["direct"]
    second = records["second"]
    other_direct = records["second-direct"]
    left = records["branch-left"]
    right = records["branch-right"]
    owners = records["branch-owners"]
    if created[0] != first[0] or first[0] != first[2]:
        raise ValueError("direct identity call changed first allocation identity")
    if second[0] == created[0]:
        raise ValueError("distinct source allocations were conflated")
    if other_direct[0] != created[0] or other_direct[2] != second[0]:
        raise ValueError("second direct call modified first allocation identity")
    if other_direct[4] != second[0] or other_direct[3] != other_direct[5]:
        raise ValueError("second direct call changed allocation identity or source count")
    if other_direct[0] == other_direct[4]:
        raise ValueError("first allocation's credit was credited to second")
    if not (left[0] == left[2] == first[0] and left[4] == second[0]):
        raise ValueError("true branch did not select the first allocation")
    if not (right[0] == first[0] and right[2] == right[4] == second[0]):
        raise ValueError("false branch did not select the second allocation")
    if not (owners[0] == owners[2] == first[0] and
            owners[4] == owners[6] == second[0] and
            owners[0] != owners[4]):
        raise ValueError("branch successors conflated two source allocations")
    if owners[1] != owners[3] or owners[5] != owners[7]:
        raise ValueError("same source allocation has different reference counts")
    if records["closure"][0] != first[0] or records["closure"][2] != first[0]:
        raise ValueError("closure return changed source allocation identity")
    graph = records["graph-before"]
    if len({graph[i] for i in (0, 2, 4, 6)}) != 4:
        raise ValueError("nested children have non-distinct allocation identities")
    after = records["graph-after"]
    if after[0] != graph[4] or after[2] != graph[6]:
        raise ValueError("two-level release changed retained descendant identities")
    if after[1] != 1 or after[3] != 1:
        raise ValueError("retained descendants did not each hold one source credit")


def checked(path: str) -> dict[str, list[int]]:
    records = parse(Path(path).read_text(encoding="utf-8").splitlines())
    audit(records)
    return records


def self_test() -> None:
    base = [
        "TRACE create 1 1",
        "TRACE direct 1 2 1 2",
        "TRACE second 2 1",
        "TRACE second-direct 1 2 2 2 2 2",
        "TRACE branch-left 1 3 1 3 2 2",
        "TRACE branch-right 1 3 2 3 2 3",
        "TRACE branch-owners 1 3 1 3 2 3 2 3",
        "TRACE closure 1 4 1 4",
        "TRACE graph-before 3 1 4 1 5 2 6 2",
        "TRACE graph-after 5 1 6 1",
    ]
    audit(parse(base))
    for old, new in [
        ("TRACE second-direct 1 2 2 2 2 2", "TRACE second-direct 1 2 2 2 1 2"),
        ("TRACE branch-owners 1 3 1 3 2 3 2 3", "TRACE branch-owners 1 3 1 3 2 3 1 3"),
        ("TRACE graph-after 5 1 6 1", "TRACE graph-after 5 1 6 2"),
    ]:
        bad = [new if s == old else s for s in base]
        try:
            audit(parse(bad))
        except ValueError:
            pass
        else:
            raise AssertionError("object-identity auditor accepted tampered source credits")
    print("trace_identity_negative_controls=PASS")


if __name__ == "__main__":
    if sys.argv[1:] == ["--self-test"]:
        self_test()
    elif len(sys.argv) == 3:
        c = checked(sys.argv[1])
        rust = checked(sys.argv[2])
        if c != rust:
            raise SystemExit("Lean C and generated Rust source object trace mismatch")
        print("trace_distinct_call_and_branch_objects=PASS")
    else:
        raise SystemExit("usage: check-object-identity-transfers.py --self-test | lean-c.txt rust.txt")
