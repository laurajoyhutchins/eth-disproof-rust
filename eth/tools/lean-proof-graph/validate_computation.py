#!/usr/bin/env python3
"""Fail-closed validation and mobile projection for compiled Lean expression graphs.

Completeness here means a closed source-package *definition-reference* export;
it does not mean runtime control-flow completeness, physical parity, or a
mathematical equivalence proof between the original algorithms.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

PINS = {
    "openai": (
        "7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a",
        "d13f23b723b8a846827a245b89c10fc7d3f11612",
        "4.34.1",
    ),
    "anthropic": (
        "16a5ce41304fcdaea4e0be7c132e1c361dc26da5",
        "0df444a360eaa60ab8c11dca51a86af692955474",
        "4.33.1",
    ),
}
KINDS = {
    "sequence", "loop", "branch", "call", "base", "bind",
    "sum-range", "fold-range", "product-range", "query",
    "lift", "optional-bind", "substitution", "recursion",
    "atom-set", "atom-copy", "atom-not", "atom-and", "atom-or",
    "atom-xor", "atom-push", "atom-peek", "atom-pop",
}
DECL_KINDS = {
    "definition", "opaque", "theorem-boundary", "axiom-boundary",
    "inductive-boundary", "constructor-boundary", "recursor-boundary",
    "quotient-boundary",
}
AST_PATH = re.compile(r"0(?:\.(?:[0-9]+|body|type|value|project|metadata|fn))*\Z")


def check(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_computation(path: Path) -> tuple[dict, dict[str, dict], int]:
    manifest = None
    nodes: dict[str, dict] = {}
    footer = None
    operations = 0
    with path.open("r", encoding="utf-8") as handle:
        for number, line in enumerate(handle, 1):
            check(line.strip() != "", f"blank computation JSONL record at line {number}")
            item = json.loads(line)
            check(type(item) is dict, f"non-object record at line {number}")
            if number == 1:
                check(
                    item.get("kind") == "manifest"
                    and item.get("protocol") == "original-computational-expr-v1"
                    and item.get("complete") is False
                    and item.get("source") in PINS
                    and isinstance(item.get("module"), str)
                    and type(item.get("original_modules")) is int
                    and item["original_modules"] > 0
                    and isinstance(item.get("roots"), list)
                    and item["roots"]
                    and all(isinstance(x, str) and x for x in item["roots"])
                    and len(set(item["roots"])) == len(item["roots"]),
                    "invalid or incomplete computation manifest",
                )
                manifest = item
                continue
            check(footer is None, "records follow terminal computation footer")
            if item.get("kind") == "complete":
                footer = item
                continue
            check(item.get("kind") == "declaration", f"non-declaration at line {number}")
            name = item.get("id")
            check(isinstance(name, str) and name and name not in nodes,
                  f"duplicate or empty declaration at line {number}")
            check(isinstance(item.get("defining_module"), str)
                  and item.get("declaration_kind") in DECL_KINDS
                  and type(item.get("body_available")) is bool,
                  f"missing declaration metadata for {name}")
            for field in ("project_refs", "external_refs"):
                values = item.get(field)
                check(isinstance(values, list)
                      and all(isinstance(v, str) and v for v in values)
                      and len(set(values)) == len(values),
                      f"invalid or duplicate {field} for {name}")
            check(not set(item["project_refs"]) & set(item["external_refs"]),
                  f"project/external reference overlap for {name}")
            ops = item.get("operators")
            check(isinstance(ops, list), f"missing operator occurrences for {name}")
            observed = set()
            for op in ops:
                check(isinstance(op, dict), f"non-object operator for {name}")
                p = op.get("path")
                check(isinstance(p, str) and AST_PATH.fullmatch(p)
                      and p not in observed, f"duplicate or invalid AST path for {name}")
                observed.add(p)
                check(isinstance(op.get("operator"), str)
                      and op.get("control_kind") in KINDS
                      and type(op.get("arity")) is int
                      and op["arity"] > 0,
                      f"invalid operator classification for {name}#{p}")
                effects = op.get("operand_effects")
                effect_fields = (
                    "reg_reads_arg_positions", "reg_writes_arg_positions",
                    "stack_reads_arg_positions", "stack_writes_arg_positions",
                )
                check(type(effects) is dict and set(effects) == set(effect_fields),
                      f"invalid typed operand effects for {name}#{p}")
                for field in effect_fields:
                    values = effects[field]
                    check(isinstance(values, list) and
                          all(type(i) is int and 0 <= i < op["arity"]
                              for i in values) and
                          len(set(values)) == len(values),
                          f"bad {field} for {name}#{p}")
                heads = op.get("argument_heads")
                check(isinstance(heads, list) and len(heads) == op["arity"]
                      and all(h is None or isinstance(h, str) for h in heads),
                      f"invalid argument heads for {name}#{p}")
            check(item["body_available"] or not ops,
                  f"operator claimed without a body in {name}")
            operations += len(ops)
            nodes[name] = item
    check(manifest is not None, "missing manifest")
    check(footer is not None, "incomplete export: terminal footer absent")
    check(footer.get("nodes") == len(nodes)
          and footer.get("operators") == operations
          and footer.get("roots") == manifest["roots"],
          "completion counters or roots inconsistent")
    check(set(manifest["roots"]).issubset(nodes),
          "missing declared computational roots")
    missing = [(name, dest)
               for name, row in nodes.items()
               for dest in row["project_refs"] if dest not in nodes]
    check(not missing, f"unresolved project references: {missing[:4]}")
    return manifest, nodes, operations


def make_view(path: Path, source_sha: str, mathlib_sha: str,
              lean_version: str) -> dict:
    manifest, nodes, operator_count = read_computation(path)
    source = manifest["source"]
    check((source_sha, mathlib_sha, lean_version) == PINS[source],
          f"source/Mathlib/Lean pin mismatch for {source}")
    project_edges = [
        {"from": owner, "to": dest, "kind": "elaborated-value-reference"}
        for owner in sorted(nodes)
        for dest in nodes[owner]["project_refs"]
    ]
    operator_rows = [
        {"owner": owner, **op}
        for owner in sorted(nodes)
        for op in nodes[owner]["operators"]
    ]
    boundary = sum(1 for n in nodes.values() if not n["body_available"])
    external_count = sum(len(n["external_refs"]) for n in nodes.values())
    return {
        "schema": "original-computational-expr-view-v1",
        "source": source,
        "source_sha": source_sha,
        "mathlib_sha": mathlib_sha,
        "lean_version": lean_version,
        "module": manifest["module"],
        "original_modules": manifest["original_modules"],
        "roots": manifest["roots"],
        "raw_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "raw_complete": True,
        "view_is_projection": True,
        "scope": "reachable source-package constant-value references",
        "evidence": "Lean.Environment.checked original elaborated definition bodies",
        "limitations": [
            "Operator occurrences record elaborated syntax, not complete dynamic control flow.",
            "External libraries and theorem bodies remain explicit unexpanded boundaries.",
            "No source-level line locations or sound register read/write effects are inferred.",
            "No mathematical equivalence, physical execution parity, or complexity claim.",
        ],
        "counts": {
            "declarations": len(nodes),
            "operator_occurrences": operator_count,
            "project_reference_edges": len(project_edges),
            "external_reference_occurrences": external_count,
            "unexpanded_nondefinition_boundaries": boundary,
        },
        "nodes": [
            {
                "id": name,
                "module": item["defining_module"],
                "kind": item["declaration_kind"],
                "body_available": item["body_available"],
                "operator_count": len(item["operators"]),
                "external_reference_count": len(item["external_refs"]),
            }
            for name, item in sorted(nodes.items())
        ],
        "edges": project_edges,
        "operators": operator_rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--mathlib-sha", required=True)
    parser.add_argument("--lean-version", required=True)
    args = parser.parse_args()
    view = make_view(args.input, args.source_sha, args.mathlib_sha,
                     args.lean_version)
    summary = {k: view[k] for k in
               ("schema", "source", "source_sha", "mathlib_sha",
                "lean_version", "roots", "original_modules", "counts", "raw_sha256", "scope",
                "limitations")}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(view, separators=(",", ":"), sort_keys=True) + "\n")
    args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
