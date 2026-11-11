#!/usr/bin/env python3
"""Single resumable entry point for source-pinned Lean -> Rust generation.

This is a thin orchestration layer over the existing strict exporter and
receipt-verifying Rust compiler. It never fabricates source tables or evidence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import time
from pathlib import Path
import subprocess
import sys

from extract_compiled_catalog import discover
from export_compiled_batch import (SOURCE_SHA, MATHLIB_SHA, blob_hash,
                                   ensure_pinned, exporter_fingerprint, verified_receipt)

TOOLS = Path(__file__).resolve().parent
REPO = TOOLS.parents[2]
DEFAULT_SOURCE = REPO / "upstream/openai-math"
DEFAULT_LAKE = REPO / "instrumentation/lean-env"
DEFAULT_OUTPUT = REPO / ".lean-rust"

def identity(record: dict) -> str:
    return hashlib.sha256(json.dumps({
        "source": SOURCE_SHA, "mathlib": MATHLIB_SHA,
        "declaration": record["fqn"], "blob": record["git_blob"],
        "exporter": exporter_fingerprint(),
    }, sort_keys=True).encode()).hexdigest()[:24]

def resolve(candidates: list[dict], selector: str) -> dict:
    matches = [r for r in candidates if selector in (r["id"], r["fqn"])]
    if len(matches) != 1:
        raise ValueError(f"expected one original declaration for {selector!r}; found {len(matches)}")
    return matches[0]

def valid_cached(folder: Path, rec: dict, max_labels: int = 8192) -> bool:
    """A cached result needs a validated individual receipt AND a matching batch."""
    receipt = verified_receipt(folder, rec, max_labels)
    if receipt is None:
        return False
    try:
        batch = json.loads((folder / "batch-report.json").read_text())
        return (batch.get("kind") == "original-source-program-export"
                and receipt in batch.get("exported", [])
                and batch.get("pins") == receipt["pins"])
    except (OSError, ValueError, TypeError, KeyError):
        return False


def doctor(upstream: Path, lake: Path) -> int:
    """Check prerequisites without modifying or downloading the source tree."""
    print(f"Original source: {upstream}")
    print(f"Pinned Lake root: {lake}")
    try:
        pins = ensure_pinned(upstream, lake)
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        print(f"NOT READY: {error}", file=sys.stderr)
        return 1
    print(f"READY: original {pins['source_commit'][:12]}, "
          f"Mathlib {pins['mathlib_commit'][:12]}, {pins['lean']}")
    return 0


def execute(argv: list[str], *, stage: str, folder: Path) -> None:
    """Preserve a reproducible failure bundle without inventing success."""
    folder.mkdir(parents=True, exist_ok=True)
    log = folder / (stage + ".log")
    metadata = folder / (stage + ".json")
    started = time.monotonic()
    print("+", " ".join(argv), flush=True)
    with log.open("w", encoding="utf-8") as stream:
        result = subprocess.run(argv, cwd=REPO, stdout=stream, stderr=subprocess.STDOUT,
                                check=False)
    report = {"stage": stage, "command": argv, "cwd": str(REPO),
              "exit_code": result.returncode, "elapsed_seconds": round(time.monotonic()-started, 3),
              "log": str(log)}
    metadata.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    if result.returncode:
        tail = log.read_text(errors="replace")[-2000:]
        raise RuntimeError(f"{stage} failed (exit {result.returncode}); {log}\n{tail}")
    print(f"{stage}: complete in {report['elapsed_seconds']}s; log={log}")

def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--upstream", type=Path, default=DEFAULT_SOURCE)
    p.add_argument("--lake-root", type=Path, default=DEFAULT_LAKE)
    p.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    sub = p.add_subparsers(dest="command", required=True)
    sub.add_parser("doctor")
    listing = sub.add_parser("list")
    listing.add_argument("--filter", default="", help="substring of declaration or ID")
    for name in ("export", "generate", "build", "status", "verify"):
        command = sub.add_parser(name)
        command.add_argument("program")
        if name in ("export", "build"):
            command.add_argument("--timeout-seconds", type=int, default=240)
            command.add_argument("--max-labels", type=int, default=4096)
            command.add_argument("--no-build", action="store_true")
        if name == "status":
            command.add_argument("--json", action="store_true")
        if name == "build":
            command.add_argument("--verify", action="store_true",
                                 help="refuse until independent differential verification is available")
    a = p.parse_args()
    if a.command == "doctor":
        return doctor(a.upstream, a.lake_root)
    if a.command == "verify":
        raise RuntimeError("independent original-Lean/Rust state comparison is not wired; refusing verified status")
    if a.command == "build" and a.verify:
        raise RuntimeError("independent Lean/Rust differential verification not wired; refusing verified status")
    inventory = discover(a.upstream, True)["candidates"]
    if a.command == "list":
        for r in inventory:
            if a.filter.casefold() in (r["id"] + " " + r["fqn"]).casefold():
                print(r["id"], r["fqn"])
        return 0
    rec = resolve(inventory, a.program)
    source_file = a.upstream / rec["file"]
    if blob_hash(source_file.read_bytes()) != rec["git_blob"]:
        raise ValueError("pinned original Lean source blob changed")
    folder = a.output_dir / identity(rec)
    tables = folder / "tables"
    generated = folder / "rust"
    if a.command == "status":
        state = {"declaration": rec["fqn"], "cache": str(folder),
                 "exported": valid_cached(tables, rec),
                 "generated_file_present": (generated / (rec["id"] + ".rs")).is_file(),
                 "generated_verified": False}
        if a.json:
            print(json.dumps(state, indent=2))
        else:
            print(rec["fqn"])
            print(f"  Original table: {'EXPORTED' if state['exported'] else 'NOT EXPORTED'}")
            print(f"  Rust source:    {'PRESENT (unverified)' if state['generated_file_present'] else 'NOT GENERATED'}")
            print("  Lean/Rust differential: NOT VERIFIED")
            print(f"  Cache: {folder}")
        return 0
    if a.command in ("export", "build"):
        ensure_pinned(a.upstream, a.lake_root)
        if not valid_cached(tables, rec, a.max_labels):
            execute([sys.executable, str(TOOLS / "export_compiled_batch.py"),
                     "--upstream", str(a.upstream), "--lake-root", str(a.lake_root),
                     "--output-dir", str(tables), "--query-closure",
                     "--name-regex", "^" + re.escape(rec["fqn"]) + "$",
                     "--limit", "1", "--max-labels", str(a.max_labels),
                     "--timeout-seconds", str(a.timeout_seconds)]
                    + (["--no-build"] if a.no_build else []), stage="export", folder=folder)
        else:
            print("REUSED validated original Lean table", rec["id"])
    if a.command in ("generate", "build"):
        label_budget = a.max_labels if a.command == "build" else 8192
        if not valid_cached(tables, rec, label_budget):
            raise ValueError("missing verified source table; run export first")
        execute([sys.executable, str(TOOLS / "compile_exported_batch.py"),
                 "--tables", str(tables), "--rust-output", str(generated),
                 "--typecheck-crate", str(folder / "typecheck"),
                 "--rust-crate", str(REPO / "rust/lean_eth_reference")], stage="generate", folder=folder)
    return 0

if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"FAILED: {error}", file=sys.stderr)
        sys.exit(1)
