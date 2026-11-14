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
import time

from export_compiled_batch import atomic_write, ensure_pinned
from extract_compiled_catalog import blob_hash
from run_source_graph_batch import LEAN as SOURCE_GRAPH_EXPORTER
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


MAX_PROCESS_OUTPUT_BYTES = 8 * 1024 * 1024
# The verified original QueryStream fresh import alone peaked at 8,460,263,424
# bytes of process-group RSS on the hosted runner (run 43632313284).
# A 5-GiB exporter limit therefore refused before entering the graph macro.
# Keep a finite bound with measured headroom, not an arbitrary lower-than-import cap.
MAX_EXPORT_RSS_BYTES = 12 * 1024 * 1024 * 1024


class ResourceLimitError(RuntimeError):
    """A supervised process exceeded its finite execution resource budget."""


class OutputLimitError(ResourceLimitError):
    """A process exceeded the finite stdout/stderr evidence budget."""


def _tail(path: Path, maximum: int = 2400) -> str:
    with path.open("rb") as stream:
        stream.seek(0, os.SEEK_END)
        stream.seek(max(0, stream.tell() - maximum), os.SEEK_SET)
        return stream.read(maximum).decode("utf8", errors="replace")


def _process_group_rss_bytes(pgid: int) -> int:
    """Best-effort Linux resident-memory guard, not virtual address space."""
    if not Path("/proc").is_dir():
        return 0
    total = 0
    for process in Path("/proc").iterdir():
        if not process.name.isdigit():
            continue
        try:
            stat = (process / "stat").read_text()
            # Linux stat fields after the closing command parenthesis:
            # state, ppid, pgrp. The command itself may contain spaces.
            fields = stat.rsplit(") ", 1)[1].split()
            if len(fields) < 3 or int(fields[2]) != pgid:
                continue
            for line in (process / "status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    total += int(line.split()[1]) * 1024
                    break
        except (OSError, ValueError, IndexError):
            continue
    return total


def run_bounded(argv: list[str], cwd: Path, timeout: int,
                env: dict[str, str] | None = None,
                log_base: Path | None = None,
                rss_limit_bytes: int | None = None) -> subprocess.CompletedProcess[str]:
    """Supervise a whole process group without unbounded output or pipe waits.

    A child in a different session can inherit a pipe and survive group kill.
    Therefore no stdout/stderr pipes or second unbounded communicate() call
    are permitted. Output is streamed into bounded disk-backed evidence; the
    supervising process keeps its own fixed wall-clock deadline.
    """
    with tempfile.TemporaryDirectory(prefix="original-query-process-") as scratch:
        root = Path(scratch)
        stdout_path = Path(str(log_base) + ".stdout.log") if log_base else root / "stdout.log"
        stderr_path = Path(str(log_base) + ".stderr.log") if log_base else root / "stderr.log"
        stdout_path.parent.mkdir(parents=True, exist_ok=True)
        stderr_path.parent.mkdir(parents=True, exist_ok=True)

        with stdout_path.open("wb") as stdout_file, stderr_path.open("wb") as stderr_file:
            child = subprocess.Popen(
                argv, cwd=cwd, env=env, stdout=stdout_file, stderr=stderr_file,
                start_new_session=True,
            )
            started = time.monotonic()
            heartbeat = 30
            peak_resident_bytes = 0
            try:
                while child.poll() is None:
                    elapsed = time.monotonic() - started
                    out_size = os.fstat(stdout_file.fileno()).st_size
                    err_size = os.fstat(stderr_file.fileno()).st_size
                    if out_size > MAX_PROCESS_OUTPUT_BYTES or err_size > MAX_PROCESS_OUTPUT_BYTES:
                        raise OutputLimitError(
                            f"bounded output exceeded {MAX_PROCESS_OUTPUT_BYTES} bytes "
                            f"(stdout={out_size} stderr={err_size})")
                    resident = (_process_group_rss_bytes(child.pid)
                                if (rss_limit_bytes is not None or log_base is not None) else 0)
                    peak_resident_bytes = max(peak_resident_bytes, resident)
                    if rss_limit_bytes is not None and resident > rss_limit_bytes:
                        raise ResourceLimitError(
                            f"original exporter RSS budget exceeded "
                            f"{rss_limit_bytes} bytes: observed {resident}")
                    if elapsed >= timeout:
                        raise TimeoutError(f"timeout {timeout}s: {argv[0]} {argv[1:3]}")
                    if log_base is not None and elapsed >= heartbeat:
                        print(f"ORIGINAL_AOT_PROCESS_PROGRESS elapsed={int(elapsed)}s "
                              f"stdout_bytes={out_size} stderr_bytes={err_size} "
                              f"peak_rss_bytes={peak_resident_bytes}", flush=True)
                        heartbeat += 30
                    time.sleep(0.2)
                if (os.fstat(stdout_file.fileno()).st_size > MAX_PROCESS_OUTPUT_BYTES
                        or os.fstat(stderr_file.fileno()).st_size > MAX_PROCESS_OUTPUT_BYTES):
                    raise OutputLimitError("bounded output exceeded after child exit")
            except (TimeoutError, ResourceLimitError) as error:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                # Never wait on inherited pipes. Even if the leader is stuck,
                # the cleanup path itself has a hard deadline.
                try:
                    child.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    child.kill()
                    try:
                        child.wait(timeout=1)
                    except subprocess.TimeoutExpired:
                        pass
                raise type(error)(
                    f"{error}; stdout_tail={_tail(stdout_path, 1200)} "
                    f"stderr_tail={_tail(stderr_path, 2400)}") from error
            finally:
                if child.poll() is None:
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                if log_base is not None:
                    print(f"ORIGINAL_AOT_PROCESS_END elapsed={int(time.monotonic()-started)}s "
                          f"exit={child.returncode} peak_rss_bytes={peak_resident_bytes}", flush=True)
        stdout = stdout_path.read_bytes().decode("utf8", errors="replace")
        stderr = stderr_path.read_bytes().decode("utf8", errors="replace")
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
                    ["lake", "env", "lean", str(import_check)], args.lake_root, 180,
                    log_base=out / "original-fresh-import")
                if checked.returncode:
                    refuse("original-module-fresh-import",
                           f"exit={checked.returncode} "
                           f"stdout_tail={checked.stdout[-2400:]} "
                           f"stderr_tail={checked.stderr[-1000:]}")
            atomic_write(out / "lean-build.log",
                         "verified original query .olean and independent fresh import\n")
        except (ValueError, OSError, TimeoutError, ResourceLimitError, json.JSONDecodeError) as error:
            refuse("original-module-import-receipt", str(error))
    else:
        try:
            built = run_bounded(["lake", "-K", f"maxJobs={args.max_jobs}", "build", MODULE],
                                args.lake_root, args.build_timeout)
            atomic_write(out / "lean-build.log", built.stdout + "\n" + built.stderr)
            if built.returncode:
                refuse("original-module-build", built.stderr[-3500:])
        except (TimeoutError, OutputLimitError) as error:
            refuse("original-module-build-resource-limit", str(error))

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
        # Compile source-graph metaprogramming once, before importing the
        # enormous original QueryStream module. Elaborating this helper after
        # importing QueryStream causes otherwise avoidable environment pressure.
        # The helper is a compiled Lean module, not a JSON compiler backend.
        exporter_module = "OriginalSourceGraphExporter"
        # Lean -o enforces the Lake package root for a compiled module.
        # An ordinary temporary file outside the root fails before parsing.
        exporter_source = args.lake_root / (exporter_module + ".lean")
        if exporter_source.exists() or exporter_source.is_symlink():
            refuse("source-graph-exporter-module-collision",
                   "refuse to replace an existing Lake-root exporter source")
        exporter_olean = (args.lake_root / ".lake/build/lib/lean" /
                          (exporter_module + ".olean"))
        exporter_olean.parent.mkdir(parents=True, exist_ok=True)
        exporter_olean.unlink(missing_ok=True)
        try:
            with exporter_source.open("xb") as output:
                output.write(SOURCE_GRAPH_EXPORTER.read_bytes())
            try:
                compiled_exporter = run_bounded(
                    ["lake", "env", "lean", "-o", str(exporter_olean),
                     str(exporter_source)], args.lake_root, args.timeout,
                    log_base=out / "source-graph-exporter-build")
            except (TimeoutError, ResourceLimitError) as error:
                refuse("source-graph-exporter-build-resource-limit", str(error))
        finally:
            exporter_source.unlink(missing_ok=True)
        if compiled_exporter.returncode or not exporter_olean.is_file():
            refuse("source-graph-exporter-build",
                   f"exit={compiled_exporter.returncode} "
                   f"stdout_tail={compiled_exporter.stdout[-2500:]} "
                   f"stderr_tail={compiled_exporter.stderr[-1500:]}")
        exporter_digest = hashlib.sha256(exporter_olean.read_bytes()).hexdigest()
        print(f"ORIGINAL_AOT_EXPORTER_PRECOMPILED olean_sha256={exporter_digest}",
              flush=True)

        lean = tmp / "QueryStream.lean"
        lean.write_text(
            f"import {exporter_module}\n"
            f"import {MODULE}\n"
            "set_option maxHeartbeats 8000000\n"
            "set_option maxRecDepth 8192\n"
            f'#export_original_source_graph {DECLARATION} "{IDENTIFIER}" "{blob}"\n',
            encoding="utf8",
        )
        try:
            exported = run_bounded(["lake", "env", "lean", str(lean)],
                                  args.lake_root, args.timeout,
                                  {**os.environ, "ORIGINAL_MAX_LABELS": str(args.max_source_labels),
                                   "ORIGINAL_SOURCE_GRAPH_TRACE": "1"},
                                  log_base=out / "original-command",
                                  rss_limit_bytes=MAX_EXPORT_RSS_BYTES)
        except (TimeoutError, OutputLimitError) as error:
            refuse("original-command-export-resource-limit", str(error))
        atomic_write(out / "lean-export.log", exported.stdout + "\n" + exported.stderr)
        if exported.returncode:
            # Lean elaboration errors often appear on stdout, not stderr.
            # Preserve both channels so a typed refusal names the actual
            # reduction/normalization phase rather than an empty reason.
            refuse("original-command-export",
                   f"exit={exported.returncode} "
                   f"stdout_tail={exported.stdout[-3500:]} "
                   f"stderr_tail={exported.stderr[-1500:]}")
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
            "source_graph_exporter_source_sha256": hashlib.sha256(
                SOURCE_GRAPH_EXPORTER.read_bytes()).hexdigest(),
            "source_graph_exporter_olean_sha256": exporter_digest,
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
