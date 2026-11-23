#!/usr/bin/env python3
"""Cross-check a native-IR ownership inventory against the existing source-IR probe.

No runtime reimplementation: this is a static shape/credit-obligation gate.
The physical Lean C vs Reader Rust event oracle is run separately, and its
result is *not* inferred from this manifest.
"""
from __future__ import annotations

import argparse
import csv
import re
from collections import Counter, defaultdict
from pathlib import Path

ROOTS = (
    "RuntimeHeapDel.rebuild",
    "RuntimeHeapDel.rebuildOrDiscard",
    "RuntimeHeapDel.rebuildOrExtract",
    "RuntimeHeapDel.rebuildThenExtract",
    "RuntimeHeapDel.rebuildOrDiscardByPayload",
    "RuntimeHeapDel.rebuildOrExtractByPayload",
)
POSITIVE = set(ROOTS[-2:])
COLUMNS = ("declaration", "path", "ordinal", "op", "subject", "detail")
SUMMARY = ("declaration", "inc", "dec", "del", "jdecl", "proj", "isShared", "set", "reset", "reuse")
COUNT_OPS = {
    "inc": "FnBody.inc",
    "dec": "FnBody.dec",
    "del": "FnBody.del",
    "jdecl": "FnBody.jdecl",
    "proj": "Expr.proj",
    "isShared": "Expr.isShared",
    "set": "FnBody.set",
    "reset": "Expr.reset",
    "reuse": "Expr.reuse",
}
PATH = re.compile(r"root(?:/(?:join|cont|alt)_[0-9]+)*\Z")
VAR = re.compile(r"x_[0-9]+\Z")
CREDIT = re.compile(r"n=[0-9]+/check=(?:true|false)/persistent=(?:true|false)\Z")


def rows(path: Path, schema: tuple[str, ...]) -> list[dict[str, str]]:
    with path.open(newline="") as inp:
        reader = csv.DictReader(inp, delimiter="\t")
        if tuple(reader.fieldnames or []) != schema:
            raise ValueError(f"{path}: unexpected schema {reader.fieldnames}")
        records = list(reader)
    if any(not v or any("\n" in item for item in v.values()) for v in records):
        raise ValueError(f"{path}: empty, null, or newline field")
    return records


def check(
    records: list[dict[str, str]],
    counts: list[dict[str, str]],
    oracle: list[dict[str, str]],
    reader_source: str | None = None,
) -> None:
    if [r["declaration"] for r in counts] != list(ROOTS):
        raise ValueError("native root set/order differs from original source")
    if [r["declaration"] for r in oracle] != list(ROOTS):
        raise ValueError("independent final-IR probe root set/order differs")
    grouped: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in records:
        root = row["declaration"]
        if root not in ROOTS:
            raise ValueError(f"fabricated/foreign declaration {root}")
        if not PATH.fullmatch(row["path"]):
            raise ValueError(f"malformed structural IR path {row['path']}")
        if row["op"] not in set(COUNT_OPS.values()) | {
            "FnBody.case", "FnBody.ret", "FnBody.jmp", "FnBody.unreachable",
            "FnBody.setTag", "FnBody.uset", "FnBody.sset",
            "Expr.ctor", "Expr.uproj", "Expr.sproj", "Expr.fap", "Expr.pap",
            "Expr.ap", "Expr.box", "Expr.unbox", "Expr.lit.num",
            "Expr.lit.str", "Alt",
        }:
            raise ValueError(f"unexpected or missing IR operation {row['op']}")
        if row["op"] in {"FnBody.inc", "FnBody.dec"}:
            if not VAR.fullmatch(row["subject"]) or not CREDIT.fullmatch(row["detail"]):
                raise ValueError("lost source credit flags or reference identity")
        if row["op"] == "FnBody.del":
            if row["detail"] != "shell-only" or not VAR.fullmatch(row["subject"]):
                raise ValueError("shell deletion has fabricated semantics")
        if row["op"] == "FnBody.jdecl" and not row["subject"].startswith("j_"):
            raise ValueError("join identity missing")
        grouped[root].append(row)
    if set(grouped) != set(ROOTS):
        raise ValueError("missing source declaration's manifest")
    for root, summary, independent in zip(ROOTS, counts, oracle, strict=True):
        entries = grouped[root]
        if [int(e["ordinal"]) for e in entries] != list(range(len(entries))):
            raise ValueError(f"missing, reordered, or repeated event ordinal for {root}")
        observed = Counter(e["op"] for e in entries)
        for key, op in COUNT_OPS.items():
            if str(observed[op]) != summary[key]:
                raise ValueError(f"{root} {key}: count disagrees with real IR inventory")
        if summary["del"] != independent["final_ir_del"]:
            raise ValueError(f"{root}: independent source-del probe disagrees")
        if summary["jdecl"] != independent["final_ir_jdecl"]:
            raise ValueError(f"{root}: independent join probe disagrees")
        if root in POSITIVE:
            if observed["FnBody.del"] != 1 or observed["FnBody.jdecl"] != 2:
                raise ValueError(f"{root}: positive source ownership witness lost")
            needed = {"FnBody.dec", "FnBody.jmp", "Expr.proj", "Expr.isShared"}
            if any(observed[op] == 0 for op in needed):
                raise ValueError(f"{root}: missing path-sensitive credit/CFG evidence")
            if all(e["path"] == "root" for e in entries):
                raise ValueError(f"{root}: nested control-flow was flattened")
        elif observed["FnBody.del"] != 0:
            raise ValueError(f"{root}: negative source-IR witness gained deletion")
    if reader_source is not None:
        if reader_source.count(".source_del();") != 1:
            raise ValueError("Reader-generated Rust must retain one real source_del")
        if "Generated directly from Lean IR declaration: RuntimeHeapDel.rebuildOrExtractByPayload" not in reader_source:
            raise ValueError("Reader output missing original declaration provenance")


def self_test(
    records: list[dict[str, str]], counts: list[dict[str, str]],
    oracle: list[dict[str, str]]
) -> None:
    def mutated(mutate):
        r = [dict(x) for x in records]
        c = [dict(x) for x in counts]
        o = [dict(x) for x in oracle]
        mutate(r, c, o)
        try:
            check(r, c, o)
        except ValueError:
            return
        raise ValueError("mutation incorrectly accepted")
    mutated(lambda r, c, o: c[-1].__setitem__("del", "0"))
    mutated(lambda r, c, o: o[-1].__setitem__("final_ir_del", "0"))
    mutated(lambda r, c, o: r.pop(next(i for i, x in enumerate(r) if x["op"] == "FnBody.del")))
    mutated(lambda r, c, o: next(x for x in r if x["op"] == "FnBody.del").__setitem__("detail", "recursive"))
    mutated(lambda r, c, o: next(x for x in r if x["op"] == "FnBody.dec").__setitem__("detail", "n=1/check=unknown/persistent=false"))
    mutated(lambda r, c, o: next(x for x in r if x["op"] == "FnBody.jdecl").__setitem__("path", "root/forged"))
    mutated(lambda r, c, o: next(x for x in r if x["op"] == "FnBody.jdecl").__setitem__("op", "FnBody.ret"))
    print("lean_native_ownership_manifest_mutations=7/7_REFUSED")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("counts", type=Path)
    parser.add_argument("independent", type=Path)
    parser.add_argument("--reader-source", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    source = rows(args.manifest, COLUMNS)
    summary = rows(args.counts, SUMMARY)
    independent = rows(args.independent, ("declaration", "final_ir_del", "final_ir_jdecl"))
    check(source, summary, independent,
          args.reader_source.read_text() if args.reader_source else None)
    if args.self_test:
        self_test(source, summary, independent)
    print(f"lean_native_ownership_final_ir=PASS roots={len(ROOTS)} "
          f"instructions={len(source)} "
          "scope=static_IR_structure_not_physical_traces")


if __name__ == "__main__":
    main()
