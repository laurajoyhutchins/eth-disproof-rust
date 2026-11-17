#!/usr/bin/env python3
"""Fail-closed bounded source-heap event replay for separately compiled C/Rust.

The HEAP seed records are first-observation snapshots of an already
constructed graph; only retain/release records describe instrumented
explicit runtime operations. The recursive descendant releases are inferred
from source-owned child edges, then checked at live descendant boundaries.
Never read a destroyed object's physical reference-count header.
"""
from __future__ import annotations

import dataclasses
import sys
from pathlib import Path


@dataclasses.dataclass
class Node:
    count: int
    children: tuple[int, ...]


def parse(path: Path) -> list[tuple[str, tuple[int, ...]]]:
    events: list[tuple[str, tuple[int, ...]]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        words = line.split()
        if len(words) < 4 or words[0] != "HEAP":
            raise ValueError("unrecognized heap-event line")
        op = words[1]
        if op not in {"seed", "observe", "retain", "release"}:
            raise ValueError(f"unknown heap event: {op}")
        try:
            data = tuple(int(part) for part in words[2:])
        except ValueError as e:
            raise ValueError("nonnumeric heap-event input") from e
        if any(value < 0 for value in data):
            raise ValueError("negative object identity or reference count")
        if op == "seed":
            if len(data) < 3 or len(data) != 3 + data[2]:
                raise ValueError("malformed owned-field arity")
        elif len(data) != (3 if op == "retain" else 2):
            raise ValueError("incorrect heap-event arity")
        events.append((op, data))
    return events


def replay(events: list[tuple[str, tuple[int, ...]]]) -> dict[int, Node]:
    live: dict[int, Node] = {}
    ever: set[int] = set()
    order: list[str] = []

    def decrement(identity: int, ancestry: frozenset[int]) -> None:
        if identity in ancestry:
            raise ValueError("cyclic destructor graph")
        node = live.get(identity)
        if node is None or node.count < 1:
            raise ValueError("release of absent or source-freed allocation")
        if node.count > 1:
            node.count -= 1
            return
        del live[identity]
        for child in node.children:
            decrement(child, ancestry | {identity})

    for op, d in events:
        order.append(op)
        identity, count = d[0], d[1]
        if identity < 1:
            raise ValueError("zero is not a heap object identity")
        if op == "seed":
            nfields, children = d[2], d[3:]
            if identity in ever:
                raise ValueError("duplicate or recycled allocation identity")
            if count != 1 or nfields != len(children):
                raise ValueError("newly observed source allocation must own one credit")
            if len(set(children)) != len(children):
                raise ValueError("duplicate child owner edge")
            if any(c not in live for c in children):
                raise ValueError("owned child not available at seed boundary")
            ever.add(identity)
            live[identity] = Node(count, tuple(children))
        elif op == "observe":
            if identity not in live or count != live[identity].count:
                raise ValueError("physical source count disagrees with heap replay")
        elif op == "retain":
            before, after = count, d[2]
            node = live.get(identity)
            if node is None or node.count != before or after != before + 1:
                raise ValueError("missing/incorrect source retain event")
            node.count = after
        elif op == "release":
            node = live.get(identity)
            if node is None or node.count != count:
                raise ValueError("release-before count disagrees with source heap")
            decrement(identity, frozenset())

    expected_ops = (
        ["seed"] * 5 + ["observe"] * 5 + ["retain"] * 2 +
        ["release"] + ["observe"] * 2 + ["release"] * 2
    )
    if order != expected_ops:
        raise ValueError("incomplete or reordered allocation/retain/destructor schedule")
    seeds = [d for op, d in events if op == "seed"]
    grand, cousin, inner, sibling, root = [d[0] for d in seeds]
    if seeds[2][3:] != (grand, cousin) or seeds[4][3:] != (inner, sibling):
        raise ValueError("source tree edges do not match independently observed structure")
    observations = [d for op, d in events if op == "observe"]
    if [d[0] for d in observations] != [root, inner, grand, cousin, sibling, grand, sibling]:
        raise ValueError("physical observation order does not match source graph")
    retains = [d for op, d in events if op == "retain"]
    if [d[0] for d in retains] != [grand, sibling]:
        raise ValueError("wrong descendants were explicitly retained")
    releases = [d for op, d in events if op == "release"]
    if [d[0] for d in releases] != [root, grand, sibling]:
        raise ValueError("expected root and final descendant releases")
    if live:
        raise ValueError(f"destructor cascade left unexpected live source allocations: {live}")
    return live


def self_test() -> None:
    good: list[tuple[str, tuple[int, ...]]] = [
        ("seed", (3, 1, 0)), ("seed", (5, 1, 0)),
        ("seed", (2, 1, 2, 3, 5)), ("seed", (4, 1, 0)),
        ("seed", (1, 1, 2, 2, 4)),
        ("observe", (1, 1)), ("observe", (2, 1)),
        ("observe", (3, 1)), ("observe", (5, 1)), ("observe", (4, 1)),
        ("retain", (3, 1, 2)), ("retain", (4, 1, 2)),
        ("release", (1, 1)),
        ("observe", (3, 1)), ("observe", (4, 1)),
        ("release", (3, 1)), ("release", (4, 1)),
    ]
    replay(good)
    mutants: list[list[tuple[str, tuple[int, ...]]]] = []
    for index, changed in [
        (10, ("retain", (3, 1, 3))),  # fabricated credit
        (11, ("retain", (4, 2, 3))),  # missing physical inc
        (12, ("release", (1, 2))),   # wrong release pre-count
        (2, ("seed", (2, 1, 2, 3, 3))),  # aliased owned fields
        (3, ("seed", (3, 1, 0))),    # duplicate allocation
        (13, ("observe", (3, 2))),  # fake post-cascade count
    ]:
        bad = list(good)
        bad[index] = changed
        mutants.append(bad)
    mutants.append(good[:11] + good[12:])  # omitted retain
    for bad in mutants:
        try:
            replay(bad)
        except ValueError:
            pass
        else:
            raise AssertionError("heap replay accepted an adversarial event sequence")
    print("heap_event_adversarial_refusals=7/7:PASS")


def main() -> None:
    if sys.argv[1:] == ["--self-test"]:
        self_test()
        return
    if len(sys.argv) != 3:
        raise SystemExit("usage: check-heap-events.py --self-test | c-events.txt rust-events.txt")
    c_events = parse(Path(sys.argv[1]))
    r_events = parse(Path(sys.argv[2]))
    replay(c_events)
    replay(r_events)
    if c_events != r_events:
        raise ValueError("independent C and generated Rust source-heap events disagree")
    print(f"physical_heap_event_replay={len(c_events)}_source_events:PASS")


if __name__ == "__main__":
    main()
