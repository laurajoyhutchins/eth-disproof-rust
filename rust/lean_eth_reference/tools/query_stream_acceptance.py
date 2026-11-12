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

    built = subprocess.run(["lake", "-K", "maxJobs=2", "build", MODULE],
                           cwd=args.lake_root, capture_output=True, text=True,
                           timeout=args.timeout_seconds)
    atomic_write(output/"original-build.log", built.stdout+"\n"+built.stderr)
    if built.returncode:
        fail("source-build", built.stderr[-4000:]+built.stdout[-2000:])

    with tempfile.TemporaryDirectory(prefix="original-query-stream-") as temp:
        src = Path(temp)/"QueryStreamExport.lean"
        src.write_text(source(record), encoding="utf8")
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
        code = generate_rust_query_test(root, abi)
        project = Path(temp)/"crate"
        (project/"src").mkdir(parents=True)
        (project/"tests").mkdir()
        (project/"src/lib.rs").write_text("// Actual Lean-origin program, no host counting oracle\n")
        (project/"tests/query.rs").write_text(code)
        (project/"Cargo.toml").write_text(
            isolated_cargo_manifest("original_query_stream_check", args.rust_crate))
        atomic_write(output/"query-stream.generated.rs", code)
        tested = subprocess.run(
            ["cargo", "test", "--offline", "--manifest-path", str(project/"Cargo.toml")],
            capture_output=True, text=True, timeout=args.timeout_seconds)
        atomic_write(output/"rust-compile.log", tested.stdout+"\n"+tested.stderr)
        if tested.returncode:
            fail("generated-rust-compile", tested.stderr[-6000:]+tested.stdout[-3000:])

    evidence = {"status": "SOURCE_GRAPH_COMPILED_IN_RUST",
                "declaration": DECLARATION, "source_commit": pin["source_commit"],
                "source_blob": blob, "graph_sha256": hashlib.sha256(raw).hexdigest(),
                "generated_rust_sha256": hashlib.sha256(code.encode()).hexdigest(),
                "physical_labels": abi[2], "entry": abi[3], "nodes_bounded": MAX_NODES,
                "independent_full_physical_parity": False,
                "kernel_certificate": False,
                "end_to_end_count_reconstruction": False}
    atomic_write(receipt, json.dumps(evidence, sort_keys=True, indent=2)+"\n")
    atomic_write(report, json.dumps(evidence, sort_keys=True, indent=2)+"\n")
    print(f"ORIGINAL_QUERY_STREAM_RUST_COMPILED labels={abi[2]} entry={abi[3]}", flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", required=True, type=Path)
    parser.add_argument("--lake-root", required=True, type=Path)
    parser.add_argument("--rust-crate", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--timeout-seconds", type=int, default=900)
    parser.add_argument("--max-source-labels", type=int, default=8192)
    args = parser.parse_args()
    if not 60 <= args.timeout_seconds <= 1800:
        parser.error("timeout must be 60..1800 seconds")
    if not 1 <= args.max_source_labels <= 8192:
        parser.error("original finite root size bound currently 1..8192")
    compile_query(args)


if __name__ == "__main__":
    main()
