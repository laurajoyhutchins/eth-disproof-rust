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
    "command_symbol_kinds", "same_module_local_declarations",
    "external_module_edges_unresolved", "transitive_computational_closure",
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
        "format": "original-query-kernel-root-v1",
        "status": STATUS,
        "root": DECLARATION,
        "compiler": COMPILER,
        "source_kind": "definition",
        "command_name": MODULE + ".command",
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
    print(f"ORIGINAL_QUERY_KERNEL_ROOT_OBSERVED nodes={report['expression_nodes']} "
          f"symbols={len(report['immediate_symbols'])} "
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
