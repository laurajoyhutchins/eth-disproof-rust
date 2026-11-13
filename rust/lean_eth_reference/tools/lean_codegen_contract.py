#!/usr/bin/env python3
"""Fail-closed acceptance boundary shared by Lean compiler-IR and core-Expr paths.

This establishes source-file/receipt integrity, never executable correctness.
The source file binding is NOT a proof that the named declaration comes from
that file; declaration provenance requires an independent Lean-side witness.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

MAX_BYTES = 8 * 1024 * 1024
MAX_NODES = 10_000
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
ROOT = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")
BACKENDS = {"compiler-ir": "generated-unverified", "residual-expr": "residualized-unverified"}


class Refusal(ValueError):
    pass


def require(ok: bool, message: str) -> None:
    if not ok:
        raise Refusal(message)


def unique_json(raw: bytes) -> Any:
    require(0 < len(raw) <= MAX_BYTES, "artifact or report size outside bound")
    require(not raw.startswith(b"\xef\xbb\xbf"), "UTF-8 BOM not permitted")
    try:
        raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise Refusal("artifact is not UTF-8") from exc

    def fields(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            require(key not in result, "duplicate JSON field")
            result[key] = value
        return result

    try:
        return json.loads(raw, object_pairs_hook=fields,
                          parse_constant=lambda v: (_ for _ in ()).throw(Refusal(f"nonfinite JSON: {v}")))
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise Refusal("malformed UTF-8 JSON") from exc


def exact_fields(node: Any, keys: set[str]) -> None:
    require(type(node) is dict and set(node) == keys, f"invalid {node.get('tag') if isinstance(node, dict) else 'node'} schema")


def decode_name(obj: Any, depth: int = 0) -> str:
    require(depth < 200, "Lean name exceeds depth limit")
    require(type(obj) is dict, "invalid Lean name")
    tag = obj.get("tag")
    if tag == "anonymous":
        exact_fields(obj, {"tag"})
        return ""
    if tag in ("str", "num"):
        exact_fields(obj, {"tag", "parent", "value"})
        parent = decode_name(obj["parent"], depth + 1)
        value = obj["value"]
        if tag == "str":
            require(type(value) is str and bool(value), "invalid Lean name segment")
        else:
            require(type(value) is int and 0 <= value <= 2**32 - 1, "invalid Lean numeric name")
        return f"{parent}.{value}" if parent else str(value)
    raise Refusal("unknown Lean name encoding")


def check_level(obj: Any, depth: int = 0) -> None:
    require(depth < 256 and type(obj) is dict, "invalid Lean universe level")
    tag = obj.get("tag")
    if tag == "zero":
        exact_fields(obj, {"tag"})
    elif tag == "param":
        exact_fields(obj, {"tag", "name"})
        decode_name(obj["name"])
    elif tag == "succ":
        exact_fields(obj, {"tag", "inner"})
        check_level(obj["inner"], depth + 1)
    elif tag in ("max", "imax"):
        exact_fields(obj, {"tag", "left", "right"})
        check_level(obj["left"], depth + 1)
        check_level(obj["right"], depth + 1)
    else:
        raise Refusal("unknown Lean universe level")


def check_ref(ref: Any, before: int) -> None:
    require(type(ref) is int and 0 <= ref < before, "DAG must be topological")


def validate_residual(raw: bytes, root: str) -> dict[str, Any]:
    require(raw.endswith(b"\n") and raw.count(b"\n") == 1,
            "residual must be one canonical JSON line")
    d = unique_json(raw)
    require(type(d) is dict, "residual must be an object")
    require(d.get("format") == "lean-core-expr-dag-v1" and
            d.get("status") == BACKENDS["residual-expr"], "invalid residual status or format")
    require(decode_name(d.get("source")) == root, "residual declaration identity mismatch")
    require(d.get("rust_executable") is False and d.get("physical_refinement") == "not-established",
            "residual improperly claims executable or physical verification")
    require(d.get("lean_defeq_checked") is True,
            "missing source/reduced definitional-equality check")
    nodes = d.get("nodes")
    require(type(nodes) is list and 0 < len(nodes) <= MAX_NODES, "residual node budget invalid")
    require(type(d.get("node_count")) is int and d["node_count"] == len(nodes),
            "residual node count mismatch")
    require(type(d.get("metadata_dropped")) is int and d["metadata_dropped"] >= 0,
            "invalid metadata drop count")
    for k in ("source_root", "reduced_root"):
        require(type(d.get(k)) is int and 0 <= d[k] < len(nodes), f"invalid {k}")
    require(type(d.get("beta_zeta_steps")) is int and 0 <= d["beta_zeta_steps"] <= 16,
            "invalid bounded reduction count")
    symbols = d.get("source_symbols")
    require(type(symbols) is list and all(type(s) is str for s in symbols)
            and len(set(symbols)) == len(symbols), "invalid source symbol list")
    shapes = {
        "bvar": ({"index"}, ()),
        "sort": ({"level"}, ()),
        "const": ({"name", "levels"}, ()),
        "app": ({"fn", "arg"}, ("fn", "arg")),
        "lam": ({"name", "binder", "type", "body"}, ("type", "body")),
        "forall": ({"name", "binder", "type", "body"}, ("type", "body")),
        "let": ({"name", "type", "value", "body", "nondep"}, ("type", "value", "body")),
        "nat": ({"value"}, ()),
        "string": ({"value"}, ()),
        "proj": ({"name", "index", "value"}, ("value",)),
    }
    for i, node in enumerate(nodes):
        require(type(node) is dict and node.get("tag") in shapes,
                f"unknown core Expr node at {i}")
        extras, refs = shapes[node["tag"]]
        exact_fields(node, {"tag"} | extras)
        for field in refs:
            check_ref(node[field], i)
        if node["tag"] in ("lam", "forall"):
            require(node["binder"] in ("default", "implicit", "strictImplicit", "instImplicit"),
                    "invalid binder")
        if node["tag"] in ("nat", "bvar", "proj"):
            field = "value" if node["tag"] == "nat" else "index"
            require(type(node[field]) is int and node[field] >= 0,
                    "invalid numeric core Expr component")
        if node["tag"] == "string":
            require(type(node["value"]) is str, "invalid string literal")
        if node["tag"] == "let":
            require(type(node["nondep"]) is bool, "invalid let nondep")
        if node["tag"] in ("const", "lam", "forall", "let", "proj"):
            decode_name(node["name"])
        if node["tag"] == "sort":
            check_level(node["level"])
        if node["tag"] == "const":
            require(type(node["levels"]) is list, "invalid universe list")
            for level in node["levels"]:
                check_level(level)
    return d


def validate_ir(raw: bytes, artifact: bytes, module: str, roots: list[str]) -> dict[str, Any]:
    d = unique_json(raw)
    require(type(d) is dict and d.get("format") == "lean-compiler-ir-backend-probe-v1"
            and d.get("status") == BACKENDS["compiler-ir"], "invalid compiler-IR receipt")
    require(d.get("module") == module and d.get("roots") == sorted(set(roots)),
            "IR receipt declaration identity mismatch")
    require(d.get("semantic_verification") == "not-established" and
            d.get("physical_bitprogram_verification") == "not-established",
            "IR receipt improperly claims semantic or physical verification")
    require(type(d.get("generated_bytes")) is int and d["generated_bytes"] == len(artifact)
            and d.get("generated_sha256") == hashlib.sha256(artifact).hexdigest(),
            "IR generated source digest or byte count mismatch")
    require(type(d.get("lean_toolchain")) is str and
            d["lean_toolchain"].startswith("leanprover/lean4:v"),
            "IR toolchain pin missing")
    summary = d.get("backend_summary")
    require(type(summary) is dict and summary.get("module") == module and
            type(summary.get("functions")) is int and summary["functions"] > 0 and
            summary.get("skipped") == [], "IR backend omitted or skipped closure")
    publics = summary.get("public")
    require(type(publics) is list and all(type(p) is dict and
            type(p.get("lean")) is str and type(p.get("rust")) is str for p in publics),
            "IR public declaration schema invalid")
    names = [p["lean"] for p in publics]
    require(len(set(names)) == len(names) and set(roots).issubset(names),
            "IR requested declarations missing or duplicated")
    return d


def git(repo: Path, *args: str) -> str:
    r = subprocess.run(["git", "-C", str(repo), *args], text=True,
                       capture_output=True, timeout=20, check=False)
    if r.returncode:
        raise Refusal(f"Git source identity check failed: {r.stderr.strip()[:300]}")
    return r.stdout.strip()


def source_identity(repo: Path, source_path: str, revision: str,
                    toolchain_path: str = "lean-toolchain") -> dict[str, str]:
    require(bool(HEX40.fullmatch(revision)), "source revision must be a full Git SHA")
    root = Path(git(repo, "rev-parse", "--show-toplevel")).resolve()
    require(root == repo.resolve(), "source repository path is not its Git root")
    require(git(repo, "rev-parse", "HEAD") == revision,
            "source HEAD does not equal pinned revision")
    path = (root / source_path).resolve()
    require(path.is_relative_to(root) and path.is_file(), "source file escapes Git root or is missing")
    relative = path.relative_to(root).as_posix()
    require(relative == source_path.replace("\\", "/"), "source path must be canonical")
    blob = git(repo, "rev-parse", f"{revision}:{relative}")
    require(bool(HEX40.fullmatch(blob)), "source path is not a committed Git blob")
    require(git(repo, "hash-object", relative) == blob,
            "working source file does not match pinned Git blob")
    pin_path = (root / toolchain_path).resolve()
    require(pin_path.is_relative_to(root) and pin_path.is_file(), "missing source Lean toolchain pin")
    pin_relative = pin_path.relative_to(root).as_posix()
    require(pin_relative == toolchain_path.replace("\\", "/"), "toolchain path not canonical")
    pin_blob = git(repo, "rev-parse", f"{revision}:{pin_relative}")
    require(git(repo, "hash-object", pin_relative) == pin_blob, "source Lean toolchain is not pinned")
    pin = pin_path.read_text(encoding="utf-8").strip()
    require(bool(re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+", pin)),
            "unsupported source Lean toolchain format")
    return {"git_revision": revision, "git_blob": blob, "path": relative,
            "lean_toolchain": pin, "lean_toolchain_git_blob": pin_blob,
            "lean_toolchain_path": pin_relative}


def validate_contract(*, backend: str, artifact: bytes, report: bytes | None,
                      module: str, roots: list[str], source: dict[str, str]) -> dict[str, Any]:
    require(backend in BACKENDS and bool(ROOT.fullmatch(module)), "invalid backend or module")
    require(roots and len(roots) == len(set(roots)) and
            all(bool(ROOT.fullmatch(r)) for r in roots), "invalid declaration roots")
    require(len(artifact) <= MAX_BYTES and bool(artifact), "empty or oversized generated artifact")
    if backend == "compiler-ir":
        require(report is not None, "IR path requires backend generation report")
        upstream = validate_ir(report, artifact, module, roots)
        toolchain = upstream["lean_toolchain"]
        require(toolchain == source["lean_toolchain"],
                "compiler IR toolchain differs from pinned source toolchain")
        require(type(upstream.get("lean_version")) is str and
                re.search(r"\bversion " + re.escape(toolchain.rsplit("v", 1)[-1]) + r"\b",
                          upstream["lean_version"]),
                "compiler IR actual Lean version not attested or mismatched")
    else:
        require(report is None and len(roots) == 1, "residual path accepts one root and no IR receipt")
        validate_residual(artifact, roots[0])
        toolchain = source["lean_toolchain"]
    return {
        "format": "lean-two-path-contract-v1", "backend": backend,
        "status": BACKENDS[backend], "module": module, "roots": roots,
        "source_file": source, "toolchain": toolchain,
        "artifact_sha256": hashlib.sha256(artifact).hexdigest(),
        "artifact_bytes": len(artifact),
        "checks": {"git_file_matches_head": True,
                   "backend_payload_checked": True,
                   "declaration_source_binding": "not-established",
                   "transitive_executable_closure": "not-established",
                   "residual_actual_lean_version": "not-established" if backend == "residual-expr" else "backend-reported",
                   "lean_rust_semantic_refinement": "not-established",
                   "physical_bitprogram_refinement": "not-established"},
        "executable_approved": False,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", choices=sorted(BACKENDS), required=True)
    parser.add_argument("--artifact", type=Path, required=True)
    parser.add_argument("--backend-report", type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--root", action="append", required=True)
    parser.add_argument("--source-repo", type=Path, required=True)
    parser.add_argument("--source-path", required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--source-toolchain-path", default="lean-toolchain")
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        require(args.artifact.resolve() != args.receipt.resolve(), "receipt would overwrite artifact")
        source = source_identity(args.source_repo, args.source_path, args.source_revision, args.source_toolchain_path)
        artifact = args.artifact.read_bytes()
        report = args.backend_report.read_bytes() if args.backend_report else None
        receipt = validate_contract(backend=args.backend, artifact=artifact, report=report,
                                    module=args.module, roots=args.root, source=source)
        # Never publish on rejection; inspectors treat no receipt as no acceptance.
        target = args.receipt
        target.parent.mkdir(parents=True, exist_ok=True)
        tmp = target.with_suffix(target.suffix + ".staged")
        tmp.write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n", encoding="utf-8")
        tmp.replace(target)
        print(f"validated {args.backend} receipt (NOT executable): {target}")
        return 0
    except (Refusal, OSError, subprocess.TimeoutExpired) as exc:
        # Remove a stale receipt, never let a previous pass authorize new bytes.
        args.receipt.unlink(missing_ok=True)
        print(f"two-path contract refused: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
