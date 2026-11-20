#!/usr/bin/env python3
"""Fail-closed review of the diagnostic *pinned C++* worklist trace.

The event trace comes from a separate object.cpp build, instrumented at
source-verified branch boundaries. This checker is independent of the traced
source; its tiny constructor-only reference machine checks every recorded
event, including LIFO queue order, field order, stopping at shared nodes,
and the precise pre-free checkpoint. It does NOT prove general runtime
refinement, and the ordinary uninstrumented runtime is checked separately.
"""
from __future__ import annotations

import csv
import dataclasses
import sys
from pathlib import Path

HEADER = ["case", "index", "kind", "object", "related", "field", "before", "after"]
CASES = (
    "chain1", "chain3", "chain8", "retainMid3", "retainLeaf3",
    "sharedRoot3", "forkAll", "forkRetainRight",
    "duplicateField", "diamond", "diamondRetained",
)


@dataclasses.dataclass(frozen=True)
class Event:
    kind: str
    object: str
    related: str = "_"
    field: int = 0
    before: int = 0
    after: int = 0


def reference(case: str) -> list[Event]:
    if case not in CASES:
        raise ValueError(f"unexpected worklist case: {case}")

    depths = {"chain1": 1, "chain3": 3, "chain8": 8}
    depth = depths.get(case, 3)
    nodes: dict[str, tuple[str, str]] = {}
    refs: dict[str, int] = {}
    if case.startswith("fork"):
        nodes = {
            "node:0": ("node:1", "node:4"),
            "node:1": ("node:2", "node:3"),
            "node:2": ("small:0", "witness:0"),
            "node:3": ("small:0", "witness:1"),
            "node:4": ("small:0", "witness:2"),
        }
        count = 3
    elif case == "duplicateField":
        # One allocation is owned by two fields of the SAME constructor.
        nodes = {
            "node:0": ("node:1", "node:1"),
            "node:1": ("small:0", "witness:0"),
        }
        count = 1
    elif case in ("diamond", "diamondRetained"):
        # Two parent constructors share one leaf. The right parent is
        # popped first, so only the left parent can queue the last credit.
        nodes = {
            "node:0": ("node:1", "node:2"),
            "node:1": ("node:3", "small:0"),
            "node:2": ("node:3", "small:0"),
            "node:3": ("small:0", "witness:0"),
        }
        count = 1
    else:
        count = depth
        for i in range(depth):
            next_node = f"node:{i+1}" if i+1 < depth else "small:0"
            nodes[f"node:{i}"] = (next_node, f"witness:{i}")
    refs = {name: 1 for name in nodes}
    refs.update({f"witness:{i}": 2 for i in range(count)})
    if case == "duplicateField":
        refs["node:1"] = 2
    elif case in ("diamond", "diamondRetained"):
        refs["node:3"] = 2 + (1 if case == "diamondRetained" else 0)
    if case == "retainMid3":
        refs["node:1"] += 1
    elif case == "retainLeaf3":
        refs["node:2"] += 1
    elif case == "sharedRoot3":
        refs["node:0"] += 1
    elif case == "forkRetainRight":
        refs["node:4"] += 1

    events: list[Event] = []
    # A shared root's hot-path dec never enters lean_dec_ref_cold.
    if refs["node:0"] > 1:
        return events

    pending: list[str] = []
    current: str | None = "node:0"
    freed: set[str] = set()
    while current is not None:
        if current not in nodes or current in freed or refs[current] != 1:
            raise AssertionError(f"reference entered invalid destructor: {current}")
        events.append(Event("visit", current))
        for field, target in enumerate(nodes[current]):
            events.append(Event("field", current, target, field))
            if target.startswith("small:"):
                continue
            if target in freed or target not in refs:
                raise AssertionError(f"dangling reference edge {current} -> {target}")
            if refs[target] > 1:
                before = refs[target]
                refs[target] -= 1
                events.append(Event("decrement", target, before=before, after=before-1))
            else:
                pending.append(target)
                events.append(Event("enqueue", target, before=1, after=1))
        events.append(Event("free", current))
        freed.add(current)
        if pending:
            current = pending.pop()
            events.append(Event("pop", current))
        else:
            current = None
    return events


def parse(rows: list[dict[str, str]]) -> dict[str, list[Event]]:
    groups: dict[str, list[Event]] = {}
    started: set[str] = set()
    ended: set[str] = set()
    for row in rows:
        try:
            case = row["case"]
            index = int(row["index"])
            event = Event(
                row["kind"], row["object"], row["related"],
                int(row["field"]), int(row["before"]), int(row["after"])
            )
        except (ValueError, KeyError) as e:
            raise ValueError(f"malformed internal worklist event: {row}") from e
        if case not in CASES:
            raise ValueError(f"unsupported observed case: {case}")
        if case not in groups:
            if case in started or event.kind != "BEGIN" or index != 0:
                raise ValueError(f"missing BEGIN for {case}")
            groups[case] = []
            started.add(case)
            continue
        if case in ended:
            raise ValueError(f"events after END for {case}")
        if event.kind == "END":
            if index != len(groups[case]) + 1:
                raise ValueError(f"missing internal event before END: {case}")
            ended.add(case)
            continue
        if event.kind == "BEGIN" or index != len(groups[case]) + 1:
            raise ValueError(f"reordered or duplicate event in {case}")
        groups[case].append(event)
    if list(groups) != list(CASES) or ended != set(CASES):
        raise ValueError(f"missing or reordered cases: {list(groups)}, ended={ended}")
    return groups


def audit(rows: list[dict[str, str]]) -> int:
    groups = parse(rows)
    total = 0
    for case in CASES:
        observed = groups[case]
        expected = reference(case)
        if observed != expected:
            first = next(
                (i for i, (a, b) in enumerate(zip(observed, expected)) if a != b),
                min(len(observed), len(expected)),
            )
            raise ValueError(
                f"pinned destructor worklist event mismatch {case} at {first}: "
                f"observed={observed[first:first+3]} expected={expected[first:first+3]}"
            )
        total += len(observed)
    if total < 50:
        raise ValueError("unexpectedly empty diagnostic internal-worklist evidence")
    return total


def self_test(rows: list[dict[str, str]]) -> int:
    def corrupt(case: str, kind: str, field: str, value: str) -> list[dict[str, str]]:
        output = [dict(r) for r in rows]
        matches = [r for r in output if r["case"] == case and r["kind"] == kind]
        if not matches:
            raise ValueError(f"fixture has no {kind} in {case}")
        matches[0][field] = value
        return output
    variants = [
        corrupt("chain3", "pop", "object", "node:0"),
        corrupt("chain8", "free", "object", "node:99"),
        corrupt("chain3", "enqueue", "kind", "decrement"),
        corrupt("retainMid3", "decrement", "after", "2"),
        corrupt("forkAll", "pop", "object", "node:1"),
        corrupt("forkRetainRight", "decrement", "before", "1"),
        corrupt("chain1", "field", "field", "17"),
        corrupt("chain1", "free", "kind", "visit"),
        corrupt("duplicateField", "decrement", "after", "2"),
        corrupt("diamond", "enqueue", "object", "node:2"),
        corrupt("diamondRetained", "decrement", "after", "1"),
        rows[:-1],
    ]
    for index, variant in enumerate(variants):
        try:
            audit(variant)
        except ValueError:
            continue
        raise ValueError(f"internal trace accepted mutation {index}")
    return len(variants)


def main() -> None:
    if len(sys.argv) not in (2, 3) or (len(sys.argv) == 3 and sys.argv[2] != "--self-test"):
        raise SystemExit("usage: check-internal-worklist.py EVENTS.tsv [--self-test]")
    with Path(sys.argv[1]).open(newline="", encoding="utf-8") as file:
        reader = csv.DictReader(file, delimiter="\t")
        if reader.fieldnames != HEADER:
            raise ValueError(f"diagnostic worklist schema drift: {reader.fieldnames}")
        rows = list(reader)
    total = audit(rows)
    if len(sys.argv) == 3:
        count = self_test(rows)
        print(f"worklist_internal_mutations={count}/{count}_REFUSED")
    print(f"worklist_internal_trace=PASS cases={len(CASES)} events={total} "
          "scope=PINNED_DIAGNOSTIC_CPP_SOURCE")


if __name__ == "__main__":
    main()
