#!/usr/bin/env python3
"""Bounded, source-pinned kernel-only QueryStream root inventory.

Not an AOT compiler, computational closure acceptance or parity witness.
The authoritative original .olean is freshly imported by Lean's own
kernel environment; Python only supervises and validates an evidence receipt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from export_compiled_batch import atomic_write, ensure_pinned
from extract_compiled_catalog import blob_hash
from query_stream_aot import (
    DECLARATION, LEAN_EXPORT_MEMORY_MB, MAX_EXPORT_RSS_BYTES,
    MODULE, RELATIVE, ResourceLimitError, run_bounded, verify_query_import_receipt,
)

COMPILER = "OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled"
STATUS = "SOURCE_ROOT_INVENTORIED_UNVERIFIED"
EXPECTED_FIELDS = {
    "format", "status", "root", "compiler", "source_kind",
    "immediate_symbols", "immediate_symbol_kinds", "expression_nodes", "root_app_arity",
    "command_name", "command_expression_nodes", "command_immediate_symbols",
    "command_symbol_kinds", "source_command_ir", "source_command_expanded_ir",
    "source_command_ir_resolved",
    "same_module_local_declarations",
    "external_module_edges", "external_definition_bodies",
    "second_hop_definition_bodies",
    "external_module_edges_unresolved",
    "transitive_computational_closure",
    "rust_executable",
    "independent_lean_rust_parity", "counting_parity",
    "resource_correspondence",
}


def _unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate kernel root evidence key")
        result[key] = value
    return result


def validate_kernel_root(raw: str) -> dict:
    receipt = json.loads(raw, object_pairs_hook=_unique)
    if not isinstance(receipt, dict) or set(receipt) != EXPECTED_FIELDS:
        raise ValueError("kernel root evidence has a missing or extra field")
    fixed = {
        "format": "original-query-kernel-root-v6",
        "status": STATUS,
        "root": DECLARATION,
        "compiler": COMPILER,
        "source_kind": "definition",
        "command_name": MODULE + ".command",
        "source_command_ir_resolved": False,
        "external_module_edges_unresolved": True,
        "transitive_computational_closure": False,
        "rust_executable": False,
        "independent_lean_rust_parity": False,
        "counting_parity": False,
        "resource_correspondence": False,
    }
    for name, expected in fixed.items():
        if type(receipt[name]) is not type(expected) or receipt[name] != expected:
            raise ValueError(f"kernel root evidence mismatch: {name}")
    symbols = receipt["immediate_symbols"]
    if not (isinstance(symbols, list) and 0 < len(symbols) <= 512 and
            all(isinstance(s, str) and s and len(s) <= 512 for s in symbols) and
            len(set(symbols)) == len(symbols) and COMPILER in symbols):
        raise ValueError("kernel root source symbol list invalid")
    kinds = receipt["immediate_symbol_kinds"]
    allowed = {
        "definition", "theorem", "axiom", "opaque", "inductive",
        "constructor", "recursor", "quotient",
    }
    if (not isinstance(kinds, list) or len(kinds) != len(symbols) or
            any(not isinstance(entry, dict) or
                set(entry) != {"name", "kind"} or
                entry["name"] != symbol or
                type(entry["kind"]) is not str or entry["kind"] not in allowed
                for entry, symbol in zip(kinds, symbols))):
        raise ValueError("source symbol classifications not bound to the original ordered symbols")
    nodes = receipt["expression_nodes"]
    if type(nodes) is not int or not (1 <= nodes <= 512):
        raise ValueError("kernel root expression exceeds node budget")
    if type(receipt["root_app_arity"]) is not int or receipt["root_app_arity"] != 5:
        raise ValueError("kernel source root application arity differs")
    command_symbols = receipt["command_immediate_symbols"]
    if (not isinstance(command_symbols, list) or
            not 1 <= len(command_symbols) <= 1024 or
            not all(isinstance(s, str) and s and len(s) <= 512 for s in command_symbols) or
            len(set(command_symbols)) != len(command_symbols)):
        raise ValueError("original command source symbols are invalid")
    required = {
        "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq",
        "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.prepareHigh",
        MODULE + ".nodes",
        "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command",
    }
    if not required.issubset(command_symbols):
        raise ValueError("original command high-query/nodes/reconstruction source shape differs")
    command_nodes = receipt["command_expression_nodes"]
    if type(command_nodes) is not int or not 1 <= command_nodes <= 1024:
        raise ValueError("original command expression exceeds node budget")
    command_kinds = receipt["command_symbol_kinds"]
    if (not isinstance(command_kinds, list) or
            len(command_kinds) != len(command_symbols) or
            any(not isinstance(item, dict) or
                set(item) != {"name", "kind"} or
                item["name"] != name or
                type(item["kind"]) is not str or item["kind"] not in allowed
                for item, name in zip(command_kinds, command_symbols))):
        raise ValueError("original command classifications are not bound to source symbols")
    # This source-specific first lowering is checked against the pinned
    # command AST, not merely its unordered constant set. 'seq' agrees with
    # the existing native Rust Command shape; 'unresolved' is intentionally
    # NOT a Rust Command variant and cannot silently reach execution.
    high = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.prepareHigh"
    reconstruction = (
        "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command"
    )
    def unresolved(name):
        return {"kind": "unresolved", "declaration": name,
                "source_kind": "definition"}
    expected_prefix = {
        "kind": "seq",
        "first": unresolved(high),
        "second": {
            "kind": "seq",
            "first": unresolved(MODULE + ".nodes"),
            "second": unresolved(reconstruction),
        },
    }
    if receipt["source_command_ir"] != expected_prefix:
        raise ValueError("source command IR differs from pinned original constructor order")
    expected_references = {high, MODULE + ".nodes", reconstruction}
    command_kind_by_name = {
        item["name"]: item["kind"] for item in command_kinds
    }
    if any(command_kind_by_name.get(name) != "definition"
           for name in expected_references):
        raise ValueError("source command IR references are not original definitions")

    # Exact constructor boundaries of the three original source definitions.
    # The applied reconstruction lift is a *named refusal*, not a lossless
    # translation: its finite indices and port maps have not been decoded.
    def seq(left, right):
        return {"kind": "seq", "first": left, "second": right}

    high_prefix = seq(
        unresolved("OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.resetHigh"),
        unresolved("OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.highCommand"),
    )
    nodes_prefix = seq(
        unresolved("OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.Nodes.initializeNodes"),
        seq(
            unresolved("OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.guardCursor"),
            unresolved(MODULE + ".nodeLoop"),
        ),
    )
    expanded = receipt["source_command_expanded_ir"]
    if not isinstance(expanded, dict) or set(expanded) != {"kind", "first", "second"}:
        raise ValueError("source expanded command is not a canonical sequence")
    if expanded.get("kind") != "seq" or expanded.get("first") != high_prefix:
        raise ValueError("source expanded command changed original high-query sequence")
    outer_tail = expanded.get("second")
    if (not isinstance(outer_tail, dict) or outer_tail.get("kind") != "seq" or
            outer_tail.get("first") != nodes_prefix):
        raise ValueError("source expanded command changed original node sequence")
    recon = outer_tail.get("second")
    handoff = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace.handoff"
    if (not isinstance(recon, dict) or set(recon) != {"kind", "first", "second"} or
            recon.get("kind") != "seq" or
            recon.get("first") != unresolved(handoff)):
        raise ValueError("source expanded reconstruction sequence invalid")
    lift = recon["second"]
    if (not isinstance(lift, dict) or
            set(lift) != {"kind", "declaration", "source_kind"} or
            lift.get("kind") != "unresolved" or
            lift.get("source_kind") != "application" or
            not isinstance(lift.get("declaration"), str) or
            not lift["declaration"].startswith("OAI.Algorithms.SubexponentialSAT.") or
            not lift["declaration"].endswith(".liftCommand")):
        raise ValueError("source reconstruction lift application is not an explicit refusal")
    recon_observed = next(
        (item for item in receipt["external_definition_bodies"]
         if isinstance(item, dict) and item.get("name") == reconstruction), None,
    )
    if not isinstance(recon_observed, dict) or recon_observed.get("status") != "scanned":
        raise ValueError("source reconstruction definition body is not observed")
    observed_references = dict(
        (item["name"], item["kind"])
        for item in recon_observed.get("immediate_symbol_kinds", [])
        if isinstance(item, dict) and "name" in item and "kind" in item
    )
    if observed_references.get(lift["declaration"]) != "definition":
        raise ValueError("source lift refusal head is absent from original definition")
    local = receipt["same_module_local_declarations"]
    prefix = MODULE + "."
    expected_keys = {
        "name", "kind", "body_scanned", "expression_nodes", "immediate_symbols",
    }
    if not isinstance(local, list) or not 2 <= len(local) <= 32:
        raise ValueError("same-module source declaration budget invalid")
    local_by_name = {}
    total_nodes = 0
    for item in local:
        if not isinstance(item, dict) or set(item) != expected_keys:
            raise ValueError("same-module source declaration fields invalid")
        name = item["name"]
        kind = item["kind"]
        scanned = item["body_scanned"]
        count = item["expression_nodes"]
        children = item["immediate_symbols"]
        if (type(name) is not str or not name.startswith(prefix) or
                len(name) > 512 or name in local_by_name):
            raise ValueError("same-module declaration identity or uniqueness invalid")
        if (type(kind) is not str or kind not in allowed or
                type(scanned) is not bool or scanned != (kind == "definition")):
            raise ValueError("same-module declaration proof/definition classification invalid")
        if (type(count) is not int or not 0 <= count <= 2048 or
                (scanned and count == 0) or (not scanned and count != 0)):
            raise ValueError("same-module declaration node budget or erasure claim invalid")
        if (not isinstance(children, list) or len(children) > 2048 or
                any(type(child) is not str or not child or len(child) > 512
                    for child in children) or len(set(children)) != len(children) or
                (not scanned and children)):
            raise ValueError("same-module declaration symbol list invalid")
        local_by_name[name] = item
        total_nodes += count
    if total_nodes > 8192:
        raise ValueError("same-module aggregate source node budget exceeded")
    if (DECLARATION not in local_by_name or MODULE + ".command" not in local_by_name or
            local_by_name[DECLARATION]["kind"] != "definition" or
            local_by_name[MODULE + ".command"]["kind"] != "definition"):
        raise ValueError("original root/command missing from same-module graph")
    if local_by_name[DECLARATION]["immediate_symbols"] != symbols or (
            local_by_name[MODULE + ".command"]["immediate_symbols"] != command_symbols):
        raise ValueError("same-module root/command symbols disagree with verified direct inventory")
    if (local_by_name[DECLARATION]["expression_nodes"] != nodes or
            local_by_name[MODULE + ".command"]["expression_nodes"] != command_nodes):
        raise ValueError("same-module root/command node counts disagree")
    reached = set()
    pending = [DECLARATION]
    while pending:
        current = pending.pop()
        if current in reached:
            continue
        if current not in local_by_name:
            raise ValueError(f"same-module referenced declaration missing: {current}")
        reached.add(current)
        pending.extend(child for child in local_by_name[current]["immediate_symbols"]
                       if child.startswith(prefix))
    if reached != set(local_by_name):
        raise ValueError("same-module inventory contains an unreachable declaration")

    edges = receipt["external_module_edges"]
    if not isinstance(edges, list) or not 1 <= len(edges) <= 8192:
        raise ValueError("original external declaration frontier budget invalid")
    edge_kinds = {}
    for edge in edges:
        if not isinstance(edge, dict) or set(edge) != {"from", "to", "target_kind"}:
            raise ValueError("external dependency edge fields invalid")
        source, target, kind = edge["from"], edge["to"], edge["target_kind"]
        if (type(source) is not str or type(target) is not str or
                type(kind) is not str or not source or not target or
                len(source) > 512 or len(target) > 512 or kind not in allowed):
            raise ValueError("external declaration identity or kind invalid")
        if (source not in local_by_name or
                not local_by_name[source]["body_scanned"] or
                target.startswith(prefix) or
                target not in local_by_name[source]["immediate_symbols"]):
            raise ValueError("external dependency edge is not in the original local graph")
        if (source, target) in edge_kinds:
            raise ValueError("duplicate external declaration edge")
        edge_kinds[source, target] = kind
    expected_edges = {
        (name, child)
        for name, item in local_by_name.items()
        for child in item["immediate_symbols"]
        if not child.startswith(prefix)
    }
    if set(edge_kinds) != expected_edges:
        raise ValueError("external declaration frontier is incomplete or forged")
    for source, kinds in (
        (DECLARATION, receipt["immediate_symbol_kinds"]),
        (MODULE + ".command", receipt["command_symbol_kinds"]),
    ):
        for entry in kinds:
            edge = (source, entry["name"])
            if edge in edge_kinds and edge_kinds[edge] != entry["kind"]:
                raise ValueError("external declaration kind disagrees with direct inventory")

    # Only the declaration set of the second layer is derivable from
    # first-layer body references. Type-signature references are recorded
    # separately and are not declared erased or executable.
    first_targets = {
        edge["to"] for edge in edges
        if (edge["target_kind"] == "definition" and
            edge["to"].startswith("OAI.Algorithms.SubexponentialSAT."))
    }

    def validate_bodies(items, targets, max_total, max_targets):
        if (not isinstance(items, list) or len(items) != len(targets) or
                len(items) > max_targets):
            raise ValueError("external source definition target coverage invalid")
        found = set()
        body_total = 0
        type_total = 0
        for item in items:
            if not isinstance(item, dict) or set(item) != {
                "name", "kind", "status", "expression_nodes",
                "immediate_symbols", "immediate_symbol_kinds",
                "type_status", "type_expression_nodes",
                "type_immediate_symbols", "type_symbol_kinds",
            }:
                raise ValueError("external source definition body fields invalid")
            name = item["name"]
            if (type(name) is not str or name not in targets or
                    name in found or item["kind"] != "definition"):
                raise ValueError("external source definition target missing, forged or duplicated")
            found.add(name)
            for field_prefix in ("", "type_"):
                status = item[field_prefix + "status"]
                count = item[field_prefix + "expression_nodes"]
                children = item[field_prefix + "immediate_symbols"]
                kinds = item[("type_symbol_kinds" if field_prefix
                              else "immediate_symbol_kinds")]
                if (type(status) is not str or status not in {
                    "scanned", "node_budget_refused", "aggregate_budget_refused",
                } or type(count) is not int or not 0 <= count <= 4096 or
                        not isinstance(children, list) or not isinstance(kinds, list)):
                    raise ValueError("external source definition body status/budget invalid")
                if status == "scanned":
                    if not 1 <= count <= 4096:
                        raise ValueError("scanned external definition must have actual nodes")
                elif count != 0 or children or kinds:
                    raise ValueError("refused external definition cannot claim partial source symbols")
                if (len(children) > 4096 or len(children) != len(kinds) or
                        any(type(c) is not str or not c or len(c) > 512 for c in children) or
                        len(set(children)) != len(children)):
                    raise ValueError("external source definition symbol list invalid")
                for child, kind_entry in zip(children, kinds):
                    if (not isinstance(kind_entry, dict) or
                            set(kind_entry) != {"name", "kind"} or
                            kind_entry["name"] != child or
                            type(kind_entry["kind"]) is not str or
                            kind_entry["kind"] not in allowed):
                        raise ValueError("external source definition child kind mismatch")
                if field_prefix:
                    type_total += count
                else:
                    body_total += count
        if found != targets or body_total > max_total or type_total > max_total:
            raise ValueError("external source definition coverage or aggregate budget invalid")

    first_bodies = receipt["external_definition_bodies"]
    validate_bodies(first_bodies, first_targets, 32768, 32)
    already = set(local_by_name) | first_targets
    next_targets = {
        symbol
        for item in first_bodies if item["status"] == "scanned"
        for symbol, kind in zip(item["immediate_symbols"],
                                item["immediate_symbol_kinds"])
        if (symbol.startswith("OAI.Algorithms.SubexponentialSAT.") and
            kind["kind"] == "definition" and symbol not in already)
    }
    validate_bodies(receipt["second_hop_definition_bodies"],
                    next_targets, 65536, 96)
    return receipt


def probe(args):
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    receipt_path = out / "query-kernel-root.report.json"
    receipt_path.unlink(missing_ok=True)

    def refuse(stage, detail):
        result = {"status": "REFUSED", "stage": stage, "reason": str(detail)[-4000:]}
        atomic_write(receipt_path, json.dumps(result, sort_keys=True, indent=2) + "\n")
        raise RuntimeError(f"original QueryStream kernel root {stage} refused: {detail}")

    try:
        pin = ensure_pinned(args.upstream, args.lake_root)
        blob = blob_hash((args.upstream / RELATIVE).read_bytes())
        verify_query_import_receipt(args.import_receipt, args.lake_root, blob, pin)
    except (ValueError, OSError) as error:
        refuse("pinned-import", error)

    script = Path(__file__).with_name("query_source_kernel.lean")
    try:
        run = run_bounded(
            ["lake", "env", "lean", "-j", "1", "-M", str(LEAN_EXPORT_MEMORY_MB),
             "--run", str(script), MODULE, DECLARATION, COMPILER],
            args.lake_root, args.timeout, log_base=out / "original-kernel-root",
            rss_limit_bytes=MAX_EXPORT_RSS_BYTES,
        )
        if run.returncode:
            refuse("original-kernel-import",
                   f"exit={run.returncode}; stdout_tail={run.stdout[-2000:]}; "
                   f"stderr_tail={run.stderr[-2000:]}")
        report = validate_kernel_root(run.stdout.strip())
    except (TimeoutError, ResourceLimitError, ValueError, OSError) as error:
        refuse("bounded-kernel-inventory", error)

    report.update({
        "source_git_blob": blob,
        "original_olean_sha256": hashlib.sha256(
            (args.lake_root / ".lake/build/lib/lean" /
             Path(MODULE.replace(".", "/") + ".olean")).read_bytes()
        ).hexdigest(),
        "source_commit": "4eaee87548250b2682affda7d05d947c05554bae",
        "receipt_is_kernel_certificate": False,
    })
    atomic_write(receipt_path, json.dumps(report, sort_keys=True, indent=2) + "\n")
    # This artifact is *not* an executable source graph, and deliberately
    # cannot be admitted as a StructuredCalls source graph by Rust codegen.
    prefix_receipt = {
        "format": "original-query-command-prefix-v1",
        "source_commit": report["source_commit"],
        "source_git_blob": report["source_git_blob"],
        "original_olean_sha256": report["original_olean_sha256"],
        "declaration": report["command_name"],
        "resolved": False,
        "rust_executable": False,
        "command": report["source_command_ir"],
        "expanded_command": report["source_command_expanded_ir"],
    }
    atomic_write(out / "original-command-prefix.json",
                 json.dumps(prefix_receipt, sort_keys=True, indent=2) + "\n")
    print(f"ORIGINAL_QUERY_KERNEL_ROOT_OBSERVED nodes={report['expression_nodes']} "
          f"symbols={len(report['immediate_symbols'])} "
          f"local_declarations={len(report['same_module_local_declarations'])} "
          f"external_edges={len(report['external_module_edges'])} "
          f"one_hop_targets={len(report['external_definition_bodies'])} "
          f"one_hop_scanned={sum(b['status'] == 'scanned' for b in report['external_definition_bodies'])} "
          f"second_hop_targets={len(report['second_hop_definition_bodies'])} "
          f"second_hop_scanned={sum(b['status'] == 'scanned' for b in report['second_hop_definition_bodies'])} "
          "transitive_closure=false rust_executable=false")
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--lake-root", type=Path, required=True)
    parser.add_argument("--import-receipt", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()
    if not 30 <= args.timeout <= 300:
        parser.error("kernel probe timeout must be 30..300 seconds")
    args.lake_root = args.lake_root.resolve()
    args.upstream = args.upstream.resolve()
    args.import_receipt = args.import_receipt.resolve()
    args.output_dir = args.output_dir.resolve()
    probe(args)


if __name__ == "__main__":
    main()
