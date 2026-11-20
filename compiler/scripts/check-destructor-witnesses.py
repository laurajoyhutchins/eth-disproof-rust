#!/usr/bin/env python3
"""Audit physical Lean C++ destructor-cascade effects on protected witnesses.

The C oracle invokes the *real pinned runtime* and reads only live, externally
rooted sentinel reference counts after each release. No post-free dereference,
instrumented allocator hook, or assertion of internal worklist order occurs.
The independent expected table spells out exactly where recursion stops.
"""
from __future__ import annotations

import csv
import sys
from dataclasses import dataclass
from pathlib import Path

HEADER = ["case", "phase", "index", "rootId", "witnessId", "rc"]
PHASES = ["before", "afterRoot", "afterCleanup"]
# For each tree, (number of independent sentinel leaves, witness indices
# still owned by an independently retained subtree after root release).
CASES: dict[str, tuple[int, frozenset[int]]] = {
    "chain1": (1, frozenset()),
    "chain3": (3, frozenset()),
    "chain8": (8, frozenset()),
    "retainMid3": (3, frozenset({1, 2})),
    "retainLeaf3": (3, frozenset({2})),
    "sharedRoot3": (3, frozenset({0, 1, 2})),
    "forkAll": (3, frozenset()),
    "forkRetainRight": (3, frozenset({2})),
}


@dataclass(frozen=True)
class Row:
    name: str
    phase: str
    index: int
    root_id: int
    witness_id: int
    rc: int


def parse_rows(records: list[dict[str, str]]) -> list[Row]:
    parsed = []
    for raw in records:
        try:
            parsed.append(Row(
                raw["case"], raw["phase"], int(raw["index"]),
                int(raw["rootId"]), int(raw["witnessId"]), int(raw["rc"]),
            ))
        except (KeyError, ValueError) as e:
            raise ValueError(f"invalid C worklist witness row: {raw}") from e
    return parsed


def audit(rows: list[Row]) -> int:
    cursor = 0
    for name, (count, independently_retained) in CASES.items():
        root_id: int | None = None
        first_witness_ids: list[int] = []
        for phase in PHASES:
            for index in range(count):
                if cursor >= len(rows):
                    raise ValueError(f"missing worklist witness: {name}/{phase}/{index}")
                row = rows[cursor]
                cursor += 1
                if (row.name, row.phase, row.index) != (name, phase, index):
                    raise ValueError(f"worklist case/phase/row order drift: {row}")
                if row.root_id <= 0 or row.witness_id <= 0:
                    raise ValueError(f"missing physical allocation identity: {row}")
                if root_id is None:
                    root_id = row.root_id
                elif root_id != row.root_id:
                    raise ValueError(f"root identity changed during release: {row}")
                if phase == "before":
                    if row.witness_id == root_id or row.witness_id in first_witness_ids:
                        raise ValueError(f"aliased physical sentinel identities: {row}")
                    first_witness_ids.append(row.witness_id)
                elif row.witness_id != first_witness_ids[index]:
                    raise ValueError(f"witness identity drift after release: {row}")
                expected = 1
                if phase == "before" or (phase == "afterRoot" and index in independently_retained):
                    expected = 2
                if row.rc != expected:
                    raise ValueError(
                        f"wrong real Lean C descendant credit at {name}/{phase}/"
                        f"witness{index}: expected={expected}, measured={row.rc}"
                    )
    if cursor != len(rows):
        raise ValueError(f"unconsumed worklist observations: {len(rows) - cursor}")
    return cursor


def self_test(rows: list[Row]) -> int:
    from dataclasses import replace

    def mutation_at(name: str, phase: str, index: int, **changes: object) -> list[Row]:
        result = list(rows)
        positions = [i for i, row in enumerate(result)
                     if (row.name, row.phase, row.index) == (name, phase, index)]
        if len(positions) != 1:
            raise ValueError(f"test fixture lacks mutation target: {name}/{phase}/{index}")
        i = positions[0]
        result[i] = replace(result[i], **changes)
        return result

    fixtures = [
        mutation_at("chain8", "afterRoot", 6, rc=2),
        mutation_at("retainMid3", "afterRoot", 1, rc=1),
        mutation_at("forkRetainRight", "afterRoot", 0, rc=2),
        mutation_at("forkRetainRight", "afterRoot", 2, rc=1),
        mutation_at("chain3", "afterCleanup", 2, rc=2),
        mutation_at("chain3", "afterRoot", 0, root_id=0),
        mutation_at("chain3", "afterRoot", 0, witness_id=9999999),
        rows[:3] + rows[4:],
        rows[:7] + list(reversed(rows[7:9])) + rows[9:],
    ]
    for index, altered in enumerate(fixtures):
        try:
            audit(altered)
        except ValueError:
            continue
        raise ValueError(f"witness auditor accepted corruption {index}")
    return len(fixtures)


def main() -> None:
    if len(sys.argv) not in (2, 3) or (len(sys.argv) == 3 and sys.argv[2] != "--self-test"):
        raise SystemExit("usage: check-destructor-witnesses.py TRACE.tsv [--self-test]")
    with Path(sys.argv[1]).open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f, delimiter="\t")
        if reader.fieldnames != HEADER:
            raise ValueError(f"destructor witness header drift: {reader.fieldnames}")
        rows = parse_rows(list(reader))
    count = audit(rows)
    if len(sys.argv) == 3:
        mutations = self_test(rows)
        print(f"destructor_witness_mutations={mutations}/{mutations}_REFUSED")
    print(f"destructor_worklist_witnesses=PASS cases={len(CASES)} "
          f"rows={count} physical_refcount_effects_only")


if __name__ == "__main__":
    main()
