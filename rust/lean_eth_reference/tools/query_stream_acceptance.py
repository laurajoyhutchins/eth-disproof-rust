#!/usr/bin/env python3
"""Compile the *original* QueryStreamProgram.program with the existing source compiler.

This is an integration gate, not another implementation of the query or a
semantic SAT oracle. Source/IR validity, Rust compilation, and independent
Lean parity have separate receipts. A refusal is always a failed gate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
from pathlib import Path
import subprocess
import tempfile

from export_compiled_batch import atomic_write, ensure_pinned
from extract_compiled_catalog import blob_hash
from run_source_graph_batch import HERE, LEAN, source
from temporary_rust_crate import isolated_cargo_manifest
from verify_source_graph import (
    MAX_NODES, MAX_SOURCE_LABELS, RustGenerator, insist, parse_node,
    parse_source_graph_json, number, closed_keys,
)

RELATIVE = Path("lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamProgram.lean")
MODULE = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram"
DECLARATION = MODULE + ".program"
IDENTIFIER = "query_stream_program"
EXPECTED_REGISTERS = 40
EXPECTED_STACKS = 896
EXPECTED_INPUT = 330
EXPECTED_OUTPUT = 323


def validate_query_source(raw: bytes, blob: str):
    graph = parse_source_graph_json(raw)
    closed_keys(graph, {"kind", "source_commit", "source_blob", "declaration",
                        "id", "abi", "command"})
    insist(graph["kind"] == "original-structured-source-v1",
           "unexpected original source schema")
    insist(graph["source_commit"] == "4eaee87548250b2682affda7d05d947c05554bae"
           and graph["source_blob"] == blob
           and graph["declaration"] == DECLARATION
           and graph["id"] == IDENTIFIER, "original query source identity mismatch")
    abi = graph["abi"]
    closed_keys(abi, {"r", "s", "labels", "input", "output"})
    (r, s, labels, inp, out) = (
        number(abi[field], bound, field) for field, bound in
        (("r", 256), ("s", 4096),
         ("labels", MAX_SOURCE_LABELS), ("input", 4096), ("output", 4096))
    )
    insist((r, s, inp, out) == (EXPECTED_REGISTERS, EXPECTED_STACKS,
                               EXPECTED_INPUT, EXPECTED_OUTPUT),
           "wrong actual query machine or ports")
    root = parse_node(graph["command"], r, s, [MAX_NODES])
    insist(root.size + 1 == labels, "incomplete query program compilation")
    insist(root.kind == "seq" and root.children[1].kind == "seq",
           "query program is not high preparation; nodes; reconstruction")
    return graph, root, (r, s, labels, root.entry(1, 0), inp, out)


def generate_rust_query_test(root, abi):
    r, s, labels, entry, inp, out = abi
    generator = RustGenerator(r, s)
    root_name = generator.emit(root)
    return "\n".join([
        "use std::sync::Arc;",
        "use lean_eth_reference::bit_program::{Block, DeferredProgram, Instr, Program, RunLimits, Atom};",
        f"fn query() -> Result<Arc<DeferredProgram<{r},{s}>>, lean_eth_reference::Error> {{",
        *generator.lines,
        f"    DeferredProgram::composed({inp}, {out}, {root_name})",
        "}",
        "#[test]",
        "fn genuine_query_stream_compiles_with_physical_abi() {",
        "    let p = query().unwrap();",
        f"    assert_eq!(p.labels(), {labels});",
        f"    assert_eq!(p.entry(), {entry});",
        f"    assert_eq!(p.input_stack(), {inp});",
        f"    assert_eq!(p.output_stack(), {out});",
        "    assert_eq!(p.instruction_at(0).unwrap(), Instr::Halt);",
        "    assert!(p.instruction_at(p.entry()).is_ok());",
        "    assert!(p.instruction_at(p.labels() - 1).is_ok());",
        "    let mut machine = p.initial(vec![]);",
        "    // A bounded physical step is not a semantic count reconstruction.",
        "    assert!(p.run(&mut machine, RunLimits { max_steps: 0, max_stack_bits: 4096 }).is_err());",
        "}",
        "",
    ])


def generate_rust_query_binary(root, abi):
    # Share the exact emitted source constructors with the acceptance test.
    # Nothing here changes or simulates the pinned original program.
    preamble, separator, _test = generate_rust_query_test(root, abi).partition("#[test]\\n")
    insist(bool(separator), "missing generated Rust query function")
    return preamble + (HERE/"query_stream_entrypoint.rs").read_text(encoding="utf8")


def compile_query(args):
    output = args.output_dir
    output.mkdir(parents=True, exist_ok=True)
    receipt = output/"query-stream.receipt.json"
    receipt.unlink(missing_ok=True)
    report = output/"report.json"
    def fail(stage, reason):
        atomic_write(report, json.dumps({"status": "REFUSED", "stage": stage,
                                         "detail": str(reason)}, sort_keys=True, indent=2)+"\n")
        raise RuntimeError(f"query stream {stage} refused: {reason}")

    try:
        pin = ensure_pinned(args.upstream, args.lake_root)
        original = args.upstream/RELATIVE
        blob = blob_hash(original.read_bytes())
        record = {"id": IDENTIFIER, "module": MODULE, "fqn": DECLARATION,
                  "file": str(RELATIVE), "git_blob": blob}
    except (ValueError, OSError) as error:
        fail("source-pin", error)

    try:
        built = subprocess.run(["lake", "-K", f"maxJobs={args.max_jobs}", "build", MODULE],
                               cwd=args.lake_root, capture_output=True, text=True,
                               timeout=args.build_timeout_seconds)
    except subprocess.TimeoutExpired as error:
        def diagnostic(value):
            return value.decode("utf8", errors="replace") if isinstance(value, bytes) else (value or "")
        atomic_write(output/"original-build.log",
                     diagnostic(error.stdout)+"\n"+diagnostic(error.stderr))
        fail("source-build-timeout", f"pinned module build exceeded {args.build_timeout_seconds} seconds; "
             "reusable successful Lean object files must be restored from the exact-version cache")
    atomic_write(output/"original-build.log", built.stdout+"\n"+built.stderr)
    if built.returncode:
        fail("source-build", built.stderr[-4000:]+built.stdout[-2000:])

    with tempfile.TemporaryDirectory(prefix="original-query-stream-") as temp:
        src = Path(temp)/"QueryStreamExport.lean"
        query_source = source(record).replace(
            "set_option maxHeartbeats 2000000\n",
            "set_option maxHeartbeats 8000000\nset_option maxRecDepth 8192\n")
        src.write_text(query_source, encoding="utf8")
        # Bound the real command, never turn a failure into a truncated graph.
        exported = subprocess.run(["lake", "env", "lean", str(src)],
                                  cwd=args.lake_root,
                                  env={**os.environ, "ORIGINAL_MAX_LABELS":
                                       str(args.max_source_labels)},
                                  capture_output=True, text=True,
                                  timeout=args.timeout_seconds)
        atomic_write(output/"original-export.log", exported.stdout+"\n"+exported.stderr)
        if exported.returncode:
            fail("original-command-export", exported.stderr[-6000:]+exported.stdout[-2000:])
        raw = exported.stdout.encode("ascii")
        graph_path = output/"query-stream.json"
        atomic_write(graph_path, exported.stdout)
        try:
            _graph, root, abi = validate_query_source(raw, blob)
        except (ValueError, KeyError, TypeError) as error:
            fail("source-graph-validation", error)
        r, s, labels, entry, inp, out = abi
        code = generate_rust_query_test(root, abi)
        project = Path(temp)/"crate"
        (project/"src").mkdir(parents=True)
        (project/"tests").mkdir()
        (project/"src/lib.rs").write_text("// Actual Lean-origin program, no host counting oracle\n")
        (project/"tests/query.rs").write_text(code)
        executable_source = generate_rust_query_binary(root, abi)
        (project/"src/main.rs").write_text(executable_source)
        atomic_write(output/"query-stream.executable.rs", executable_source)
        (project/"Cargo.toml").write_text(
            isolated_cargo_manifest("original_query_stream_check", args.rust_crate))
        atomic_write(output/"query-stream.generated.rs", code)
        tested = subprocess.run(
            ["cargo", "test", "--offline", "--manifest-path", str(project/"Cargo.toml")],
            capture_output=True, text=True, timeout=args.timeout_seconds)
        atomic_write(output/"rust-compile.log", tested.stdout+"\n"+tested.stderr)
        if tested.returncode:
            fail("generated-rust-compile", tested.stderr[-6000:]+tested.stdout[-3000:])

        # A real cargo binary, not merely a test harness. Check its physical
        # ports, native instruction resolver and explicit resource refusal.
        runner = ["cargo", "run", "--offline", "--quiet", "--manifest-path",
                  str(project/"Cargo.toml"), "--"]
        try:
            built_binary = subprocess.run(runner + ["abi"], capture_output=True,
                                          text=True, timeout=args.timeout_seconds)
        except subprocess.TimeoutExpired as error:
            fail("generated-binary-timeout", error)
        atomic_write(output/"rust-binary.log",
                     built_binary.stdout+"\\n"+built_binary.stderr)
        expected_abi = (f"registers={r} stacks={s} labels={labels} entry={entry} "
                        f"input={inp} output={out}")
        if built_binary.returncode or built_binary.stdout.strip() != expected_abi:
            fail("generated-binary-abi",
                 f"expected {expected_abi!r}, got {built_binary.stdout[-3000:]!r} "
                 + built_binary.stderr[-3000:])
        binary = project/"target/debug/original_query_stream_check"
        if not binary.is_file():
            fail("generated-binary-missing", "cargo did not produce executable")
        for argv, expected_status in ((["instruction", "0"], 0),
                                      (["instruction", str(entry)], 0),
                                      (["instruction", str(labels - 1)], 0),
                                      (["run-bits", "0", "0", "4096"], 1),
                                      (["run-bits", "not-binary", "100", "4096"], 1)):
            probe = subprocess.run([str(binary), *argv], capture_output=True,
                                   text=True, timeout=60)
            if (probe.returncode == 0) != (expected_status == 0):
                fail("generated-binary-execution",
                     f"{argv}: exit={probe.returncode} "
                     + probe.stdout[-1000:] + probe.stderr[-1000:])
            if argv == ["instruction", "0"] and probe.stdout.strip() != "Halt":
                fail("generated-binary-halt", probe.stdout)
        shutil.copyfile(binary, output/"query-stream")
        executable_hash = hashlib.sha256(executable_source.encode()).hexdigest()
        binary_hash = hashlib.sha256(binary.read_bytes()).hexdigest()

    evidence = {"status": "SOURCE_GRAPH_COMPILED_IN_RUST_EXECUTABLE",
                "declaration": DECLARATION, "source_commit": pin["source_commit"],
                "source_blob": blob, "graph_sha256": hashlib.sha256(raw).hexdigest(),
                "generated_rust_sha256": hashlib.sha256(code.encode()).hexdigest(),
                "generated_binary_source_sha256": executable_hash,
                "compiled_binary_sha256": binary_hash,
                "bounded_physical_cli_probe": True,
                "physical_labels": abi[2], "entry": abi[3], "nodes_bounded": MAX_NODES,
                "independent_full_physical_parity": False,
                "kernel_certificate": False,
                "end_to_end_count_reconstruction": False}
    atomic_write(receipt, json.dumps(evidence, sort_keys=True, indent=2)+"\n")
    atomic_write(report, json.dumps(evidence, sort_keys=True, indent=2)+"\n")
    print(f"ORIGINAL_QUERY_STREAM_RUST_EXECUTABLE labels={abi[2]} entry={abi[3]}", flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", required=True, type=Path)
    parser.add_argument("--lake-root", required=True, type=Path)
    parser.add_argument("--rust-crate", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--timeout-seconds", type=int, default=1200)
    parser.add_argument("--build-timeout-seconds", type=int, default=3600)
    parser.add_argument("--max-jobs", type=int, default=4)
    parser.add_argument("--max-source-labels", type=int, default=1000000000)
    args = parser.parse_args()
    if not 60 <= args.timeout_seconds <= 3600:
        parser.error("timeout must be 60..3600 seconds")
    if not 60 <= args.build_timeout_seconds <= 7200:
        parser.error("build timeout must be 60..7200 seconds")
    if not 1 <= args.max_jobs <= 8:
        parser.error("Lean parallel jobs must be 1..8")
    if not 1 <= args.max_source_labels <= 1000000000:
        parser.error("symbolic root labels must be 1..1000000000; finite table leaves remain <=4096")
    compile_query(args)


if __name__ == "__main__":
    main()
