#!/usr/bin/env python3
"""Probe a whole Lean declaration through leanfran's compiler-IR Rust backend.

This is intentionally distinct from the original BitProgram physical source
exporter: successful code generation proves neither physical-step parity nor
source equivalence. In particular, noncomputable Lean definitions may have no
compiler IR. A refusal is an accepted outcome and never publishes partial code.

Use with a version-pinned Lean package and an explicitly versioned leanfran
binary. The backend discovers ordinary executable dependencies automatically;
roots are entrypoints, not a catalog of Lean constructs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any

EXPECTED_BACKEND = "leanfran 0.6.0"
EXPECTED_GENERATOR = "4"
SUPPORTED_LEAN = "4.35.0"
ROOT_RE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")


class Refusal(Exception):
    pass


def call(command: list[str], cwd: Path, timeout: int) -> str:
    try:
        result = subprocess.run(
            command, cwd=cwd, text=True, capture_output=True, check=False,
            timeout=timeout,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise Refusal(f"command unavailable or timed out: {command[:3]}: {exc}") from exc
    if result.returncode:
        raise Refusal(
            f"command failed (exit {result.returncode}): {command[:3]}: "
            f"{(result.stderr or result.stdout)[-1600:]}"
        )
    return result.stdout.strip()


def validate_summary(value: Any, module: str, roots: list[str]) -> dict[str, Any]:
    if not isinstance(value, dict) or value.get("module") != module:
        raise Refusal("backend did not return the requested module summary")
    if "error" in value:
        raise Refusal(f"backend returned error: {value['error']}")
    publics = value.get("public")
    skipped = value.get("skipped")
    if not isinstance(publics, list) or not isinstance(skipped, list):
        raise Refusal("backend summary omits public/skipped declaration arrays")
    if not all(isinstance(x, dict) and isinstance(x.get("lean"), str)
               and isinstance(x.get("rust"), str) for x in publics):
        raise Refusal("malformed public declaration in backend summary")
    if not all(isinstance(x, dict) and isinstance(x.get("name"), str)
               and isinstance(x.get("reason"), str) for x in skipped):
        raise Refusal("malformed skipped declaration in backend summary")
    if skipped:
        examples = ", ".join(f"{x['name']}: {x['reason']}" for x in skipped[:6])
        raise Refusal(f"backend skipped declarations: {examples}")
    names = [x["lean"] for x in publics]
    if len(names) != len(set(names)):
        raise Refusal("duplicate public declarations in backend summary")
    missing = sorted(set(roots) - set(names))
    if missing:
        raise Refusal(f"requested roots not emitted: {', '.join(missing)}")
    if not isinstance(value.get("functions"), int) or value["functions"] <= 0:
        raise Refusal("backend generated no functions")
    return value


def write_report(path: Path, obj: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", dir=path.parent, encoding="utf-8",
                                     prefix=".lean-ir-report-", delete=False) as f:
        tmp = Path(f.name)
        json.dump(obj, f, indent=2, sort_keys=True)
        f.write("\n")
    os.replace(tmp, path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake-root", type=Path, required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--root", action="append", required=True,
                        help="fully qualified Lean function; repeat for additional roots")
    parser.add_argument("--output-rs", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=int, default=300)
    args = parser.parse_args(argv)
    report: dict[str, Any] = {
        "format": "lean-compiler-ir-backend-probe-v1", "module": args.module,
        "roots": sorted(set(args.root)), "status": "refused",
        "semantic_verification": "not-established",
        "physical_bitprogram_verification": "not-established",
    }
    try:
        if args.timeout_seconds < 1 or args.timeout_seconds > 3600:
            raise Refusal("timeout must be 1..3600 seconds")
        if not ROOT_RE.fullmatch(args.module) or any(
            not ROOT_RE.fullmatch(root) for root in args.root
        ):
            raise Refusal("invalid Lean module or root declaration name")
        if not args.lake_root.is_dir():
            raise Refusal("Lean project directory does not exist")
        output = args.output_rs.resolve()
        receipt = args.report.resolve()
        if output == receipt:
            raise Refusal("generated source and report paths must differ")
        pinned = (args.lake_root / "lean-toolchain").read_text(encoding="utf-8").strip()
        report["lean_toolchain"] = pinned
        if pinned != f"leanprover/lean4:v{SUPPORTED_LEAN}":
            raise Refusal(
                f"backend supports Lean {SUPPORTED_LEAN}, but project pins {pinned}. "
                "Do not silently upgrade the verified original source environment"
            )
        version = call(["lake", "env", "lean", "--version"], args.lake_root,
                       args.timeout_seconds)
        if not re.search(r"\bversion " + re.escape(SUPPORTED_LEAN) + r"\b", version):
            raise Refusal(f"actual Lean version mismatches {SUPPORTED_LEAN}: {version}")
        report["lean_version"] = version
        backend = call(["lake", "env", "leanfran", "--version"], args.lake_root,
                       args.timeout_seconds)
        if backend != EXPECTED_BACKEND:
            raise Refusal(f"expected {EXPECTED_BACKEND}, found {backend}")
        report["backend_version"] = backend
        generator = call(["lake", "env", "leanfran", "--generator-version"],
                         args.lake_root, args.timeout_seconds)
        if generator != EXPECTED_GENERATOR:
            raise Refusal(f"unexpected backend generator {generator}")
        report["generator_version"] = generator
        output.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="lean-ir-", dir=output.parent) as temp:
            staged = Path(temp) / "generated.rs"
            command = ["lake", "env", "leanfran", "module", "generate",
                       "--module-name", args.module, "--roots", *report["roots"],
                       "--output-file", str(staged), "--output", "json"]
            raw = call(command, args.lake_root, args.timeout_seconds)
            try:
                summary = validate_summary(json.loads(raw), args.module, report["roots"])
            except (json.JSONDecodeError, UnicodeError) as exc:
                raise Refusal("backend summary is not valid JSON") from exc
            if not staged.is_file() or staged.stat().st_size == 0:
                raise Refusal("backend produced no Rust source")
            data = staged.read_bytes()
            receipt_data = {**report,
                            "backend_summary": summary,
                            "generated_sha256": hashlib.sha256(data).hexdigest(),
                            "generated_bytes": len(data),
                            "status": "generated-unverified"}
            # Publish source only after validating all requested roots.
            os.replace(staged, output)
            write_report(receipt, receipt_data)
        print(f"IR backend generated {output}; semantics require independent verification")
        return 0
    except (Refusal, OSError, ValueError) as exc:
        report["reason"] = str(exc)
        write_report(args.report.resolve(), report)
        print(f"IR backend refused: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
