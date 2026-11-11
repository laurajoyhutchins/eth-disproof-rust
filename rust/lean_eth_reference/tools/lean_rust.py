#!/usr/bin/env python3
"""Single resumable entry point for source-pinned Lean -> Rust generation.

This is a thin orchestration layer over the existing strict exporter and
receipt-verifying Rust compiler. It never fabricates source tables or evidence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from extract_compiled_catalog import discover
from export_compiled_batch import SOURCE_SHA, MATHLIB_SHA, validate_table, blob_hash

TOOLS = Path(__file__).resolve().parent
REPO = TOOLS.parents[2]
DEFAULT_SOURCE = REPO / "upstream/openai-math"
DEFAULT_LAKE = REPO / "instrumentation/lean-env"
DEFAULT_OUTPUT = REPO / ".lean-rust"

def identity(record: dict) -> str:
    return hashlib.sha256(json.dumps({
        "source": SOURCE_SHA, "mathlib": MATHLIB_SHA,
        "declaration": record["fqn"], "blob": record["git_blob"],
    }, sort_keys=True).encode()).hexdigest()[:24]

def resolve(candidates: list[dict], selector: str) -> dict:
    matches = [r for r in candidates if selector in (r["id"], r["fqn"])]
    if len(matches) != 1:
        raise ValueError(f"expected one original declaration for {selector!r}; found {len(matches)}")
    return matches[0]

def valid_cached(folder: Path, rec: dict) -> bool:
    receipt_path = folder / (rec["id"] + ".receipt.json")
    table_path = folder / (rec["id"] + ".table")
    try:
        receipt = json.loads(receipt_path.read_text())
        raw = table_path.read_bytes()
        return (receipt["source_commit"] == SOURCE_SHA
                and receipt["source_git_blob"] == rec["git_blob"]
                and receipt["declaration"] == rec["fqn"]
                and receipt["status"] == "EXPORTED_FROM_PINNED_LEAN"
                and receipt["sha256"] == hashlib.sha256(raw).hexdigest()
                and receipt["bytes"] == len(raw)
                and bool(validate_table(raw.decode("ascii"), rec, 8192)))
    except (OSError, KeyError, ValueError, TypeError):
        return False

def execute(argv: list[str]) -> None:
    print("+", " ".join(argv), flush=True)
    subprocess.run(argv, cwd=REPO, check=True)

def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--upstream", type=Path, default=DEFAULT_SOURCE)
    p.add_argument("--lake-root", type=Path, default=DEFAULT_LAKE)
    p.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    sub = p.add_subparsers(dest="command", required=True)
    sub.add_parser("list")
    for name in ("export", "generate", "build", "status"):
        command = sub.add_parser(name)
        command.add_argument("program")
        if name in ("export", "build"):
            command.add_argument("--timeout-seconds", type=int, default=240)
            command.add_argument("--max-labels", type=int, default=4096)
            command.add_argument("--no-build", action="store_true")
        if name == "build":
            command.add_argument("--verify", action="store_true",
                                 help="refuse until independent differential verification is available")
    a = p.parse_args()
    inventory = discover(a.upstream, True)["candidates"]
    if a.command == "list":
        for r in inventory:
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
        print(json.dumps({"declaration": rec["fqn"], "cache": str(folder),
                          "exported": valid_cached(tables, rec),
                          "generated": (generated / (rec["id"] + ".rs")).is_file()},
                         indent=2))
        return 0
    if a.command in ("export", "build"):
        if not valid_cached(tables, rec):
            execute([sys.executable, str(TOOLS / "export_compiled_batch.py"),
                     "--upstream", str(a.upstream), "--lake-root", str(a.lake_root),
                     "--output-dir", str(tables), "--query-closure",
                     "--name-regex", "^" + __import__("re").escape(rec["fqn"]) + "$",
                     "--limit", "1", "--max-labels", str(a.max_labels),
                     "--timeout-seconds", str(a.timeout_seconds)]
                    + (["--no-build"] if a.no_build else []))
        else:
            print("REUSED verified original Lean table", rec["id"])
    if a.command in ("generate", "build"):
        if not valid_cached(tables, rec):
            raise ValueError("missing verified source table; run export first")
        execute([sys.executable, str(TOOLS / "compile_exported_batch.py"),
                 "--tables", str(tables), "--rust-output", str(generated),
                 "--typecheck-crate", str(folder / "typecheck"),
                 "--rust-crate", str(REPO / "rust/lean_eth_reference")])
    if a.command == "build" and a.verify:
        raise RuntimeError("independent Lean/Rust differential verification not wired; refusing verified status")
    return 0

if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"FAILED: {error}", file=sys.stderr)
        sys.exit(1)
