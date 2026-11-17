#!/usr/bin/env python3
"""Validate a completed Lean kernel environment JSONL graph. Fail closed."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def read_graph(path: Path):
    manifest = None
    nodes = {}
    end = None
    edges = 0
    with path.open(encoding="utf-8") as inp:
        for line_no, line in enumerate(inp, 1):
            if not line.strip():
                raise ValueError(f"blank JSONL record at {line_no}")
            record = json.loads(line)
            if line_no == 1:
                if record.get("kind") != "manifest" or record.get("complete") is not False:
                    raise ValueError("missing incomplete manifest header")
                manifest = record
                continue
            if end is not None:
                raise ValueError("data after terminal completion record")
            if record.get("kind") == "complete":
                end = record
                continue
            name = record["id"]
            if name in nodes:
                raise ValueError(f"duplicate declaration: {name}")
            if not isinstance(record.get("module"), str):
                raise ValueError(f"module missing: {name}")
            if not isinstance(record.get("kind"), str):
                raise ValueError(f"declaration kind missing: {name}")
            for field in ("type_refs", "value_refs"):
                refs = record.get(field)
                if not isinstance(refs, list) or not all(isinstance(r, str) for r in refs):
                    raise ValueError(f"invalid {field}: {name}")
                if len(refs) != len(set(refs)):
                    raise ValueError(f"duplicate reference in {field}: {name}")
                edges += len(refs)
            nodes[name] = record
    if end is None:
        raise ValueError("incomplete export: completion footer is absent")
    if end.get("nodes") != len(nodes) or end.get("edges") != edges:
        raise ValueError("completion counters disagree with actual graph")
    if end.get("roots") != manifest["roots"] or not set(manifest["roots"]).issubset(nodes):
        raise ValueError("missing or inconsistent roots")
    missing = [(name, r) for name, item in nodes.items()
               for field in ("type_refs", "value_refs")
               for r in item[field] if r not in nodes]
    if missing:
        raise ValueError(f"unresolved elaborated constant references: {missing[:5]}")
    return manifest, nodes, edges


def project_view(source: Path, prefixes: list[str], provenance: dict):
    manifest, nodes, edge_count = read_graph(source)
    local = {n for n, row in nodes.items()
             if any(row["module"].startswith(prefix) for prefix in prefixes)}
    boundary = {ref for name in local for key in ("type_refs", "value_refs")
                for ref in nodes[name][key] if ref not in local}
    visible = local | boundary
    edges = [{"from": name, "to": ref,
              "type": "elaborated_type" if key == "type_refs" else "elaborated_value"}
             for name in sorted(local)
             for key in ("type_refs", "value_refs")
             for ref in nodes[name][key]]
    return {
        "data_provenance": "Lean.Environment.checked; transitive elaborated closure in raw JSONL",
        "raw_complete": True,
        "view_is_projection": True,
        "view_scope": "project declarations plus immediate external boundary",
        "source_sha": provenance["source_sha"],
        "mathlib_sha": provenance["mathlib_sha"],
        "lean_version": provenance["lean_version"],
        "raw_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "roots": manifest["roots"],
        "project_prefixes": prefixes,
        "counts": {
            "raw_nodes": len(nodes),
            "raw_edges": edge_count,
            "project_nodes": len(local),
            "external_boundary_nodes": len(boundary),
            "hidden_external_closure_nodes": len(nodes) - len(visible),
            "project_edges": len(edges),
        },
        "nodes": [
            {"id": name, "module": nodes[name]["module"], "kind": nodes[name]["kind"],
             "scope": "project" if name in local else "external_boundary"}
            for name in sorted(visible)
        ],
        "edges": edges,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("input", type=Path)
    p.add_argument("--summary", required=True, type=Path)
    p.add_argument("--project-view", required=True, type=Path)
    p.add_argument("--project-prefix", action="append", required=True)
    p.add_argument("--source-sha", required=True)
    p.add_argument("--mathlib-sha", required=True)
    p.add_argument("--lean-version", required=True)
    args = p.parse_args()
    provenance = {"source_sha": args.source_sha, "mathlib_sha": args.mathlib_sha,
                  "lean_version": args.lean_version}
    view = project_view(args.input, args.project_prefix, provenance)
    summary = {k: view[k] for k in ("data_provenance", "raw_sha256", "roots",
                                    "source_sha", "mathlib_sha", "lean_version", "counts")}
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.project_view.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, sort_keys=True, indent=2) + "\n")
    args.project_view.write_text(json.dumps(view, sort_keys=True, separators=(",", ":")) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
