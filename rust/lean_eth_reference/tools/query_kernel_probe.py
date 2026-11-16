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
    "immediate_symbols", "expression_nodes", "root_app_arity",
    "transitive_computational_closure", "rust_executable",
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
    nodes = receipt["expression_nodes"]
    if type(nodes) is not int or not (1 <= nodes <= 512):
        raise ValueError("kernel root expression exceeds node budget")
    if type(receipt["root_app_arity"]) is not int or receipt["root_app_arity"] != 5:
        raise ValueError("kernel source root application arity differs")
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
