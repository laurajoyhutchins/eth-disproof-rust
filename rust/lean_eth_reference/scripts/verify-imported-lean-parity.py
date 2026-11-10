#!/usr/bin/env python3
"""Execute and compare pinned imported OpenAI Lean source against Rust.

Unlike the standalone comparators, this gate does not accept caller-provided
trace files or an alleged Lean-produced log. It executes the pinned sources,
checks their Git blob identities, and emits a provenance receipt only on pass.

Passing establishes fixture-snapshot parity, not machine-table identity,
TM2 refinement, a complexity bound, or the final ETH theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

CRATE = Path(__file__).resolve().parent.parent
REPO = CRATE.parent.parent
SOURCE_COMMIT = "4eaee87548250b2682affda7d05d947c05554bae"
LEAN_VERSION = "4.34.1"
SOURCE_PREFIX = "lean/OAI/Algorithms/SubexponentialSAT/"
# The Lean entrypoints import original openai/math modules and execute
# BitProgram.step. The Rust binaries execute the independently ported tables.
STAGES = {
    "high": ("lean_native_high_trace.lean", "native-high-trace", "compare-native-high-trace.py"),
    "tuple": ("lean_native_tuple_trace.lean", "native-tuple-trace", "compare-native-tuple-trace.py"),
    "query-prefix": ("lean_native_query_prefix_trace.lean", "native-query-prefix-trace", "compare-native-query-prefix-trace.py"),
    "nodes": ("lean_native_nodes_trace.lean", "native-nodes-trace", "compare-native-nodes-trace.py"),
    "layout-pair": ("lean_native_layout_pair_trace.lean", "native-layout-pair-trace", "compare-native-layout-pair-trace.py"),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_sha(data: bytes) -> str:
    header = b"blob " + str(len(data)).encode("ascii") + b"\x00"
    return hashlib.sha1(header + data).hexdigest()


def validate_manifest(manifest: dict, source_root: Path) -> dict[str, str]:
    """Check content of every pinned, tracked original source module."""
    if manifest.get("repository") != "openai/math" or manifest.get("commit") != SOURCE_COMMIT:
        raise ValueError("wrong upstream repository or source commit")
    if manifest.get("toolchain") != f"leanprover/lean4:v{LEAN_VERSION}":
        raise ValueError("wrong Lean toolchain pin")
    files = manifest.get("files")
    if not isinstance(files, dict) or not files:
        raise ValueError("source manifest must list pinned original modules")
    checked = {}
    for name, expected in files.items():
        if (not isinstance(name, str) or not name.startswith(SOURCE_PREFIX)
                or not Path(name).parts == tuple(name.split("/"))
                or any(part in (".", "..") for part in Path(name).parts)
                or not isinstance(expected, str) or len(expected) != 40
                or any(c not in "0123456789abcdef" for c in expected)):
            raise ValueError(f"invalid source manifest entry {name!r}")
        path = source_root / name
        try:
            actual = git_blob_sha(path.read_bytes())
        except OSError as exc:
            raise ValueError(f"required original Lean source missing: {name}") from exc
        if actual != expected:
            raise ValueError(f"original Lean source does not match pinned Git blob: {name}")
        checked[name] = actual
    return checked


def run(command: list[str], cwd: Path, timeout: int) -> str:
    try:
        result = subprocess.run(command, cwd=cwd, text=True, capture_output=True,
                                timeout=timeout, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise RuntimeError(f"cannot execute {command[0]}: {exc}") from exc
    if result.returncode != 0:
        raise RuntimeError(
            f"command failed ({result.returncode}): {command!r}\n"
            f"stderr: {result.stderr[-4000:]}\nstdout: {result.stdout[-2000:]}")
    return result.stdout


def verify_git_checkout(root: Path, expected: str | None, timeout: int) -> str:
    if not root.is_dir():
        raise ValueError(f"missing checkout: {root}")
    top = run(["git", "rev-parse", "--show-toplevel"], root, timeout).strip()
    if Path(top).resolve() != root.resolve():
        raise ValueError(f"not a repository root: {root}")
    head = run(["git", "rev-parse", "HEAD"], root, timeout).strip()
    if expected is not None and head != expected:
        raise ValueError(f"source checkout must be {expected}, found {head}")
    dirty = run(["git", "status", "--porcelain", "--untracked-files=no"], root, timeout)
    if dirty.strip():
        raise ValueError(f"tracked checkout contains changes: {root}")
    return head


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-repo", type=Path, required=True,
                        help="root of clean openai/math checkout at pinned commit")
    parser.add_argument("--stage", choices=["all", *STAGES], default="all")
    parser.add_argument("--receipt", type=Path, required=True,
                        help="written atomically only after every selected stage passes")
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    if args.timeout < 1:
        parser.error("--timeout must be positive")

    # Never retain a stale success artifact when a later verification fails.
    if args.receipt.exists():
        args.receipt.unlink()
    source_root = args.lean_repo.resolve()
    rust_head = verify_git_checkout(REPO, None, args.timeout)
    source_head = verify_git_checkout(source_root, SOURCE_COMMIT, args.timeout)
    manifest_path = CRATE / "reference" / "source-manifest.json"
    manifest_bytes = manifest_path.read_bytes()
    validated = validate_manifest(json.loads(manifest_bytes), source_root)
    lean_cwd = source_root / "lean"
    if not lean_cwd.is_dir():
        raise ValueError("pinned source has no lean project directory")
    version = run(["lake", "env", "lean", "--version"], lean_cwd, args.timeout).strip()
    if f"version {LEAN_VERSION}" not in version:
        raise ValueError(f"Lean compiler must be {LEAN_VERSION}, got {version!r}")

    stages = STAGES if args.stage == "all" else {args.stage: STAGES[args.stage]}
    receipt = {
        "status": "passed", "claim": "imported-source fixture snapshot parity only",
        "excluded_claims": ["complete machine refinement", "TM2 microsteps",
                            "bit complexity", "tape space", "ETH disproof"],
        "source_repository": "openai/math", "source_commit": source_head,
        "rust_commit": rust_head, "lean_version": version,
        "source_manifest_sha256": sha256(manifest_bytes),
        "pinned_original_source_blobs": validated, "stages": {},
    }
    with tempfile.TemporaryDirectory(prefix="lean-rust-parity-") as tmp:
        tmp_path = Path(tmp)
        for name, (lean_name, rust_bin, compare_name) in stages.items():
            lean_path = CRATE / "reference" / lean_name
            compare_path = CRATE / "scripts" / compare_name
            if not lean_path.is_file() or not compare_path.is_file():
                raise ValueError(f"missing parity program or comparator for {name}")
            lean_command = ["lake", "env", "lean", "--run", str(lean_path)]
            rust_command = ["cargo", "run", "--offline", "--quiet", "--bin", rust_bin]
            lean_output = run(lean_command, lean_cwd, args.timeout)
            rust_output = run(rust_command, CRATE, args.timeout)
            lean_trace = tmp_path / f"{name}.lean.trace"
            rust_trace = tmp_path / f"{name}.rust.trace"
            lean_trace.write_text(lean_output)
            rust_trace.write_text(rust_output)
            verdict = run([sys.executable, str(compare_path), "--lean", str(lean_trace),
                           "--rust", str(rust_trace)], CRATE, args.timeout).strip()
            receipt["stages"][name] = {
                "lean_runner_sha256": sha256(lean_path.read_bytes()),
                "comparator_sha256": sha256(compare_path.read_bytes()),
                "lean_command": lean_command, "rust_command": rust_command,
                "lean_stdout_sha256": sha256(lean_output.encode()),
                "rust_stdout_sha256": sha256(rust_output.encode()),
                "verdict": verdict,
            }

    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    pending = args.receipt.with_name(args.receipt.name + ".pending")
    pending.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    pending.replace(args.receipt)
    print(f"PASS: {len(stages)} independently executed Lean/Rust fixture suites; "
          "no theorem or TM2 resource claim")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, RuntimeError, OSError, json.JSONDecodeError) as exc:
        print(f"FAIL CLOSED: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
