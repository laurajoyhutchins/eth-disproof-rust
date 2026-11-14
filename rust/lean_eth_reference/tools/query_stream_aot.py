#!/usr/bin/env python3
"""Attempt exact pinned original QueryStream -> source graph -> native Rust AOT.

This is an integration probe, not a #SAT oracle or kernel certificate for the
full QueryStream. Every failure is recorded as a refusal, not a partial success.
The only codegen engine is the Rust original-source-codegen binary.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile

from export_compiled_batch import atomic_write, ensure_pinned
from extract_compiled_catalog import blob_hash
from run_source_graph_batch import source
from temporary_rust_crate import isolated_cargo_manifest
from verify_source_graph import (
    MAX_NODES, MAX_SOURCE_LABELS, closed_keys, insist, number,
    parse_node, parse_source_graph_json, rust_instr,
)

RELATIVE = Path("lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamProgram.lean")
MODULE = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram"
DECLARATION = MODULE + ".program"
IDENTIFIER = "query_stream_program"
SOURCE_COMMIT = "4eaee87548250b2682affda7d05d947c05554bae"


def run_bounded(argv: list[str], cwd: Path, timeout: int,
                env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    """Reap Lake/Lean descendant workers on refusal, before saving any cache."""
    child = subprocess.Popen(argv, cwd=cwd, env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, start_new_session=True)
    try:
        stdout, stderr = child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as error:
        os.killpg(child.pid, signal.SIGKILL)
        stdout, stderr = child.communicate()
        raise TimeoutError(
            f"timeout {timeout}s: {argv[0]} {argv[1:3]}; "
            f"last stderr={stderr[-2400:]}"
        ) from error
    return subprocess.CompletedProcess(argv, child.returncode, stdout, stderr)



def verify_query_import_receipt(receipt: Path, lake_root: Path, blob: str,
                                pin: dict[str, str]) -> None:
    """Verify a fresh pinned original .olean before skipping a redundant build.

    The JSON is not a certificate. Independently check the exact module bytes
    and import again in a fresh Lean process after this function returns.
    """
    if not receipt.is_file() or receipt.stat().st_size > 65536:
        raise ValueError("missing or over-budget original Lean import receipt")

    def unique(pairs):
        out = {}
        for name, value in pairs:
            if name in out:
                raise ValueError("duplicate original Lean import receipt field")
            out[name] = value
        return out

    report = json.loads(receipt.read_text(encoding="utf8"), object_pairs_hook=unique)
    if not isinstance(report, dict):
        raise ValueError("invalid original Lean import receipt")
    exact = {
        "status": "PINNED_ORIGINAL_LEAN_IMPORT_VERIFIED",
        "stage": "query",
        "module": MODULE,
        "source_commit": SOURCE_COMMIT,
        "source_git_blob": blob,
        "mathlib_commit": pin["mathlib_commit"],
        "lean_toolchain": "leanprover/lean4:v4.34.1",
        "lean_version": pin["lean"],
        "query_stream_executable": False,
        "source_graph_compiled": False,
        "independent_lean_rust_parity": False,
        "math_or_resource_theorem": False,
    }
    for key, expected in exact.items():
        if type(report.get(key)) is not type(expected) or report[key] != expected:
            raise ValueError(f"original Lean import receipt mismatch: {key}")
    digest = report.get("module_olean_sha256")
    if not isinstance(digest, str) or len(digest) != 64 or any(
            c not in "0123456789abcdef" for c in digest):
        raise ValueError("invalid original Lean module .olean digest")
    artifact = (lake_root / ".lake/build/lib/lean" /
                Path(MODULE.replace(".", "/") + ".olean"))
    if not artifact.is_file() or artifact.is_symlink():
        raise ValueError("original QueryStream .olean missing or linked")
    with artifact.open("rb") as binary:
        observed = hashlib.file_digest(binary, "sha256").hexdigest()
    if observed != digest:
        raise ValueError("original QueryStream .olean bytes differ from verified import receipt")


def validate_query(raw: bytes, blob: str):
    graph = parse_source_graph_json(raw)
    closed_keys(graph, {"kind", "source_commit", "source_blob",
                        "declaration", "id", "abi", "command"})
    insist(graph["kind"] == "original-structured-source-v1", "query graph root is not a command")
    insist((graph["source_commit"], graph["source_blob"], graph["declaration"], graph["id"]) ==
           (SOURCE_COMMIT, blob, DECLARATION, IDENTIFIER), "original query source identity differs")
    abi = graph["abi"]
    closed_keys(abi, {"r", "s", "labels", "input", "output"})
    r = number(abi["r"], 256, "registers")
    s = number(abi["s"], 4096, "stacks")
    labels = number(abi["labels"], MAX_SOURCE_LABELS, "labels")
    inp = number(abi["input"], s, "input")
    out = number(abi["output"], s, "output")
    insist((r, s, inp, out) == (40, 896, 330, 323), "original QueryStream physical ABI differs")
    root = parse_node(graph["command"], r, s, [MAX_NODES])
    insist(root.kind == "seq" and root.children[1].kind == "seq",
           "original high-query/nodes/reconstruction composition differs")
    insist(root.size + 1 == labels, "source-derived query physical label space incomplete")
    return root, (r, s, labels, root.entry(1, 0), inp, out)


def compile_query(args):
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    receipt = out / "query-stream.receipt.json"
    receipt.unlink(missing_ok=True)
    published_binary = out / "query-stream"
    published_binary.unlink(missing_ok=True)

    def refuse(stage: str, details: str):
        report = {"status": "REFUSED", "stage": stage, "reason": str(details)[-5000:]}
        atomic_write(out / "report.json", json.dumps(report, sort_keys=True, indent=2) + "\n")
        raise RuntimeError(f"original QueryStream {stage} refused: {details}")

    try:
        pin = ensure_pinned(args.upstream, args.lake_root)
        blob = blob_hash((args.upstream / RELATIVE).read_bytes())
    except (ValueError, OSError) as error:
        refuse("pin", str(error))
    record = {"id": IDENTIFIER, "fqn": DECLARATION,
              "module": MODULE, "git_blob": blob}
    if args.import_receipt is not None:
        try:
            verify_query_import_receipt(args.import_receipt, args.lake_root, blob, pin)
            with tempfile.TemporaryDirectory(prefix="original-query-import-") as scratch:
                import_check = Path(scratch) / "CheckQueryStream.lean"
                import_check.write_text(f"import {MODULE}\n", encoding="utf8")
                checked = run_bounded(
                    ["lake", "env", "lean", str(import_check)], args.lake_root, 180)
                if checked.returncode:
                    refuse("original-module-fresh-import", checked.stderr[-3500:])
            atomic_write(out / "lean-build.log",
                         "verified original query .olean and independent fresh import\n")
        except (ValueError, OSError, TimeoutError, json.JSONDecodeError) as error:
            refuse("original-module-import-receipt", str(error))
    else:
        try:
            built = run_bounded(["lake", "-K", f"maxJobs={args.max_jobs}", "build", MODULE],
                                args.lake_root, args.build_timeout)
            atomic_write(out / "lean-build.log", built.stdout + "\n" + built.stderr)
            if built.returncode:
                refuse("original-module-build", built.stderr[-3500:])
        except TimeoutError as error:
            refuse("original-module-build-timeout", str(error))

    # Bind the eventual native AOT report to the exact original module bytes,
    # not merely to a source file's Git blob or an untrusted JSON receipt.
    original_olean = (args.lake_root / ".lake/build/lib/lean" /
                      Path(MODULE.replace(".", "/") + ".olean"))
    if not original_olean.is_file() or original_olean.is_symlink():
        refuse("original-module-artifact", "verified original QueryStream .olean is missing")
    with original_olean.open("rb") as binary:
        original_olean_digest = hashlib.file_digest(binary, "sha256").hexdigest()
    import_receipt_digest = (hashlib.sha256(args.import_receipt.read_bytes()).hexdigest()
                             if args.import_receipt is not None else None)

    with tempfile.TemporaryDirectory(prefix="original-query-aot-") as scratch:
        tmp = Path(scratch)
        lean = tmp / "QueryStream.lean"
        lean.write_text(
            source(record).replace("set_option maxHeartbeats 2000000\n",
                                   "set_option maxHeartbeats 8000000\nset_option maxRecDepth 8192\n"),
            encoding="utf8",
        )
        try:
            exported = run_bounded(["lake", "env", "lean", str(lean)],
                                  args.lake_root, args.timeout,
                                  {**os.environ, "ORIGINAL_MAX_LABELS": str(args.max_source_labels),
                                   "ORIGINAL_SOURCE_GRAPH_TRACE": "1"})
        except TimeoutError as error:
            refuse("original-command-export-timeout", str(error))
        atomic_write(out / "lean-export.log", exported.stdout + "\n" + exported.stderr)
        if exported.returncode:
            refuse("original-command-export", exported.stderr[-5000:])
        raw = exported.stdout.encode("utf8")
        try:
            root, abi = validate_query(raw, blob)
        except (KeyError, TypeError, ValueError) as error:
            refuse("source-graph-validation", str(error))
        graph_file = out / "query-stream.source.json"
        graph_file.write_bytes(raw)
        digest = hashlib.sha256(raw).hexdigest()
        project = tmp / "native"
        (project / "src").mkdir(parents=True)
        source_file = project / "src/main.rs"
        # The assertion digest is computed from the graph itself, *not*
        # a Lean kernel certificate. It must not be called proof evidence.
        generated = run_bounded(
            ["cargo", "run", "--locked", "--offline", "--quiet",
             "--manifest-path", str(args.rust_crate / "Cargo.toml"),
             "--bin", "original-source-codegen", "--",
             str(graph_file), IDENTIFIER, DECLARATION, blob, digest, str(source_file)],
            args.lake_root, args.timeout)
        if generated.returncode:
            refuse("native-aot-emission", generated.stderr[-4000:])
        source_text = source_file.read_text()
        (project / "Cargo.toml").write_text(
            isolated_cargo_manifest("query_stream_native_aot", args.rust_crate))
        built = run_bounded(["cargo", "build", "--offline", "--manifest-path",
                             str(project / "Cargo.toml")], args.lake_root, args.timeout)
        atomic_write(out / "rust-build.log", built.stdout + "\n" + built.stderr)
        if built.returncode:
            refuse("native-aot-build", built.stderr[-4000:])
        binary = project / "target/debug/query_stream_native_aot"
        if not binary.is_file():
            refuse("native-binary-missing", "Cargo succeeded without the expected native executable")
        r, s, labels, entry, inp, outstack = abi
        # This is structural self-consistency with the exported graph.
        # Independent original Lean physical-state certification remains open.
        probes = sorted(set([0, entry, labels // 2, labels - 1]))
        for pc in probes:
            instruction = ('halt', ()) if pc == 0 else root.instr(1, 0, pc)
            checked = run_bounded([str(binary), "lookup", str(pc)],
                                  args.lake_root, 20)
            expected = rust_instr(instruction).removeprefix("Instr::")
            if checked.returncode or checked.stdout.strip() != expected:
                refuse("native-instruction-lookup",
                       f"pc={pc} expected={expected} got={checked.stdout[-300:]} {checked.stderr[-300:]}")
        refusal = run_bounded([str(binary), "run", "0", "0", "1024"],
                              args.lake_root, 20)
        if refusal.returncode == 0:
            refuse("bounded-physical-refusal", "zero-step limit was ignored")
        summary = {
            "status": "SOURCE_GRAPH_NATIVE_AOT_UNCERTIFIED",
            "source_commit": SOURCE_COMMIT,
            "lean_version": pin["lean"],
            "source_blob": blob,
            "original_module_olean_sha256": original_olean_digest,
            "original_module_import_receipt_sha256": import_receipt_digest,
            "original_module_import_method": (
                "verified-stage-receipt" if args.import_receipt is not None
                else "direct-pinned-Lake-build"),
            "declaration": DECLARATION,
            "id": IDENTIFIER,
            "graph_sha256": digest,
            "generated_rust_sha256": hashlib.sha256(source_text.encode()).hexdigest(),
            "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
            "physical_abi": {"r": r, "s": s, "labels": labels,
                             "entry": entry, "input": inp, "output": outstack},
            "source_nodes_budget": MAX_NODES,
            "sampled_physical_instructions": len(probes),
            "independent_lean_physical_parity": False,
            "kernel_certificate": False,
            "correct_count_reconstruction": False,
            "full_prepared_input_execution": False,
        }
        # Publish the verified native executable *before* the success receipt.
        # The receipt is the only success marker. A failed attempt clears both
        # the previous receipt and binary before any new build is attempted.
        staging = out / ".query-stream-partial"
        try:
            shutil.copyfile(binary, staging)
            staging.replace(published_binary)
        finally:
            staging.unlink(missing_ok=True)
        atomic_write(out / "report.json", json.dumps(summary, sort_keys=True, indent=2) + "\n")
        atomic_write(receipt, json.dumps(summary, sort_keys=True, indent=2) + "\n")
        atomic_write(out / "query-stream.generated.rs", source_text)
        print(f"ORIGINAL_QUERY_AOT_SOURCE_COMPILED labels={labels} nodes_budget={MAX_NODES}")
        return summary


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--lake-root", type=Path, required=True)
    parser.add_argument("--rust-crate", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=1200)
    parser.add_argument("--build-timeout", type=int, default=3600)
    parser.add_argument("--import-receipt", type=Path,
                        help="Require an independently verified full QueryStream Lean stage receipt; never blindly skip Lake")
    parser.add_argument("--max-jobs", type=int, default=4)
    parser.add_argument("--max-source-labels", type=int, default=1_000_000_000)
    args = parser.parse_args()
    if not (60 <= args.timeout <= 3600 and 60 <= args.build_timeout <= 7200
            and 1 <= args.max_jobs <= 8 and 1 <= args.max_source_labels <= 1_000_000_000):
        parser.error("invalid bounded Lean build/export parameters")
    args.lake_root = args.lake_root.resolve()
    args.rust_crate = args.rust_crate.resolve()
    args.upstream = args.upstream.resolve()
    args.output_dir = args.output_dir.resolve()
    if args.import_receipt is not None:
        args.import_receipt = args.import_receipt.resolve()
    compile_query(args)


if __name__ == "__main__":
    main()
