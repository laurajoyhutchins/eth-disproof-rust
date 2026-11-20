#!/usr/bin/env python3
"""Audit source-origin ownership events from real Lean C and exact Reader Rust.

Events are observed by wrappers around primitive *call sites*, not substituted
primitive implementations. The original compiler-generated C translation units
and the canonical Reader-generated Rust body are never rewritten.

This audit covers the explicitly instrumented inc/dec/dec_ref/del/alloc_ctor/
ctor_set call sites. Recursive C++ destructor worklist internals are *not*
individually instrumented and must not be claimed as an equal full heap trace.
"""
from __future__ import annotations

import csv
import dataclasses
import sys
from collections import defaultdict
from pathlib import Path

COLUMNS = ["case", "lane", "index", "op", "object", "related", "field", "before", "after"]
CASES = set(range(8))
LANES = ("lean-c", "reader-rust")
OPCODES = {"inc", "dec", "del", "alloc", "set"}


@dataclasses.dataclass(frozen=True)
class Event:
    op: str
    obj: str
    related: str
    field: int
    before: int
    after: int

    @property
    def signature(self) -> tuple[str, str, str, int, int]:
        # Physical absolute counts for the shared old heap stamp differ:
        # the C and Rust input parents coexist while called sequentially.
        # Compare each recorded ownership *transition*, not raw RC baselines.
        return (self.op, self.obj, self.related, self.field,
                self.after - self.before)


def audit_rows(rows: list[dict[str, str]]) -> dict[tuple[int, str], list[Event]]:
    lanes: dict[tuple[int, str], list[Event]] = defaultdict(list)
    started: set[tuple[int, str]] = set()
    finished: set[tuple[int, str]] = set()
    for row in rows:
        try:
            case, step = int(row["case"]), int(row["index"])
            field, before, after = (int(row[k]) for k in ("field", "before", "after"))
        except (ValueError, KeyError) as exc:
            raise ValueError(f"invalid event row: {row}") from exc
        lane, op = row["lane"], row["op"]
        if case not in CASES or lane not in LANES:
            raise ValueError(f"unexpected event lane or case: {case}, {lane}")
        key = (case, lane)
        if op == "BEGIN":
            if key in started or step != 0 or row["object"] != "_":
                raise ValueError(f"duplicate or malformed BEGIN: {key}")
            started.add(key)
            continue
        if key not in started or key in finished:
            raise ValueError(f"event outside active call: {key}/{op}")
        if op == "END":
            if step != len(lanes[key]) + 1 or row["object"] != "_":
                raise ValueError(f"invalid END index: {key}")
            finished.add(key)
            continue
        if op not in OPCODES or step != len(lanes[key]) + 1:
            raise ValueError(f"unknown/unordered operation {key}/{step}/{op}")
        obj, related = row["object"], row["related"]
        if not obj or obj == "_":
            raise ValueError(f"missing owned object identity at {key}/{step}")
        if before < 0 or after < 0:
            raise ValueError(f"negative reference count at {key}/{step}")
        if op == "inc" and after != before + 1:
            raise ValueError(f"invalid physical increment at {key}/{step}")
        if op == "dec" and (before <= 0 or after != before - 1):
            raise ValueError(f"invalid physical decrement at {key}/{step}")
        if op == "del" and (before != 1 or after != 0):
            raise ValueError(f"invalid shell deletion at {key}/{step}")
        if op == "alloc" and (before != 0 or after != 1 or field != 2):
            raise ValueError(f"invalid 2-field constructor allocation at {key}/{step}")
        if op == "set" and (before != after or field not in (0, 1)):
            raise ValueError(f"invalid field move at {key}/{step}")
        lanes[key].append(Event(op, obj, related, field, before, after))
    needed = {(case, lane) for case in CASES for lane in LANES}
    if started != needed or finished != needed:
        raise ValueError(f"incomplete lanes: {sorted(needed - finished)}")
    if any(not lanes[key] for key in needed):
        raise ValueError("empty source function event trace")
    return lanes


def compare(lanes: dict[tuple[int, str], list[Event]]) -> None:
    for case in sorted(CASES):
        c = lanes[(case, "lean-c")]
        r = lanes[(case, "reader-rust")]
        c_signatures = [e.signature for e in c]
        r_signatures = [e.signature for e in r]
        if c_signatures != r_signatures:
            prefix = 0
            while (prefix < min(len(c), len(r))
                   and c_signatures[prefix] == r_signatures[prefix]):
                prefix += 1
            raise ValueError(
                f"case={case} source ownership events disagree at {prefix}: "
                f"lean-c={c_signatures[prefix:prefix+4]} "
                f"reader-rust={r_signatures[prefix:prefix+4]} "
                f"lengths={len(c)}/{len(r)}"
            )


def check(rows: list[dict[str, str]]) -> dict[tuple[int, str], list[Event]]:
    lanes = audit_rows(rows)
    compare(lanes)
    return lanes


def self_test(rows: list[dict[str, str]]) -> None:
    if not rows:
        raise ValueError("missing fixture")
    for description, mutate in (
        ("missing operation", lambda r: r.pop(next(i for i, v in enumerate(r)
             if v["op"] in OPCODES))),
        ("bad reference-count delta", lambda r: next(v for v in r
             if v["op"] == "inc").__setitem__("after", "999999")),
        ("changed lane", lambda r: next(v for v in r
             if v["op"] == "BEGIN").__setitem__("lane", "host")),
        ("wrong identity", lambda r: next(v for v in r
             if v["op"] in OPCODES).__setitem__("object", "tampered")),
    ):
        copy = [dict(x) for x in rows]
        try:
            mutate(copy)
        except StopIteration as exc:
            raise ValueError("self-test needs an inc operation") from exc
        try:
            check(copy)
        except ValueError:
            continue
        raise ValueError(f"audit accepted {description} corruption")


def main() -> None:
    if len(sys.argv) not in (2, 3) or (len(sys.argv) == 3 and sys.argv[2] != "--self-test"):
        raise SystemExit("usage: check-source-del-events.py TRACE.tsv [--self-test]")
    with Path(sys.argv[1]).open(newline="") as file:
        reader = csv.DictReader(file, delimiter="\t")
        if reader.fieldnames != COLUMNS:
            raise SystemExit(f"source event TSV schema drift: {reader.fieldnames}")
        rows = list(reader)
    lanes = check(rows)
    if len(sys.argv) == 3:
        self_test(rows)
        print("source_del_event_mutations=MISSING_DELTA_LANE_IDENTITY_REFUSED")
    print("source_del_original_C_vs_exact_Reader_event_parity=PASS "
          f"cases=8 lanes=16 events={sum(map(len, lanes.values()))} "
          "boundary=source_visible_ownership_primitives")


if __name__ == "__main__":
    main()
