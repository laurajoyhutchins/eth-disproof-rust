"""Fail-closed contracts for compiling the original, four-stage query command."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from query_stream_acceptance import (
    DECLARATION, IDENTIFIER, validate_query_source, generate_rust_query_test,
    generate_rust_query_binary,
)

from temporary_rust_crate import isolated_cargo_manifest

SOURCE_SHA = "4eaee87548250b2682affda7d05d947c05554bae"
CRATE = Path(__file__).resolve().parents[1]
BLOB = "a" * 40


def atom(dst):
    return {"kind": "atom", "opcode": f"set:{dst}:1"}


def query_graph():
    # This synthetic command only tests parser contracts. Production acceptance
    # always loads the pinned original QueryStreamProgram.program in Lean.
    stages = {"kind": "seq", "first": atom(0),
              "second": {"kind": "seq", "first": atom(1),
                         "second": atom(2)}}
    return {"kind": "original-structured-source-v1",
            "source_commit": SOURCE_SHA, "source_blob": BLOB,
            "declaration": DECLARATION, "id": IDENTIFIER,
            "abi": {"r": 40, "s": 896, "labels": 4,
                    "input": 330, "output": 323}, "command": stages}


def serialized(value):
    return (json.dumps(value, separators=(",", ":")) + "\n").encode("ascii")


class QueryStreamCompilationContract(unittest.TestCase):
    def test_exact_query_abi_and_four_part_composition(self):
        _graph, root, abi = validate_query_source(serialized(query_graph()), BLOB)
        self.assertEqual(abi, (40, 896, 4, 1, 330, 323))
        rust = generate_rust_query_test(root, abi)
        self.assertIn("DeferredProgram::composed(330, 323", rust)
        self.assertIn("assert_eq!(p.labels(), 4)", rust)
        self.assertEqual(rust.count("Block::seq("), 2)
        self.assertNotIn("sat_oracle", rust.lower())

    @unittest.skipUnless(shutil.which("cargo"), "Rust compiler unavailable")
    def test_native_query_entrypoint_compiles_and_refuses_bounded_run(self):
        # Tests the real generated Rust backend with a tiny synthetic graph.
        # It does not claim that the original giant QueryStream has built.
        _graph, root, abi = validate_query_source(serialized(query_graph()), BLOB)
        binary_source = generate_rust_query_binary(root, abi)
        self.assertIn("fn main()", binary_source)
        self.assertIn('command == "run-bits"', binary_source)
        with tempfile.TemporaryDirectory(prefix="query-stream-rust-smoke-") as temp:
            project = Path(temp)
            (project/"src").mkdir()
            (project/"src/main.rs").write_text(binary_source)
            (project/"Cargo.toml").write_text(
                isolated_cargo_manifest("query_stream_smoke", CRATE))
            cmd = ["cargo", "run", "--offline", "--quiet",
                   "--manifest-path", str(project/"Cargo.toml"), "--"]
            run = subprocess.run(cmd + ["abi"], capture_output=True,
                                 text=True, timeout=180)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(run.stdout.strip(),
                             "registers=40 stacks=896 labels=4 entry=1 input=330 output=323")
            binary = project/"target/debug/query_stream_smoke"
            instruction = subprocess.run([str(binary), "instruction", "0"],
                                         capture_output=True, text=True, timeout=15)
            self.assertEqual(instruction.returncode, 0, instruction.stderr)
            self.assertEqual(instruction.stdout.strip(), "Halt")
            refused = subprocess.run([str(binary), "run-bits", "0", "0", "10"],
                                     capture_output=True, text=True, timeout=15)
            self.assertNotEqual(refused.returncode, 0)
            self.assertNotIn("HALT", refused.stdout)

    def test_no_partial_graph_masquerades_as_complete_query(self):
        bad = query_graph()
        bad["command"] = atom(0)
        bad["abi"]["labels"] = 2
        with self.assertRaisesRegex(ValueError, "not high preparation"):
            validate_query_source(serialized(bad), BLOB)

    def test_stage_omission_changes_size_and_is_rejected(self):
        bad = query_graph()
        bad["abi"]["labels"] = 3
        with self.assertRaisesRegex(ValueError, "incomplete query"):
            validate_query_source(serialized(bad), BLOB)

    def test_wrong_source_identity_is_not_accepted(self):
        for key, value in (("source_commit", "0"*40),
                           ("source_blob", "b"*40),
                           ("id", "toy"),
                           ("declaration", "OAI.Algorithms.SubexponentialSAT.Other.program")):
            with self.subTest(key=key):
                bad = query_graph()
                bad[key] = value
                with self.assertRaisesRegex(ValueError, "source identity"):
                    validate_query_source(serialized(bad), BLOB)

    def test_export_diagnostics_never_contaminate_certified_json(self):
        # Instrumentation is stderr-only. It must not introduce a second JSON
        # line or alter the SHA-256-bound source graph stdout protocol.
        exporter = (Path(__file__).parent / "export_source_graph.lean").read_text()
        runner = (Path(__file__).parent / "query_stream_acceptance.py").read_text()
        self.assertIn("ORIGINAL_SOURCE_GRAPH_TRACE", runner)
        self.assertIn("SOURCE_GRAPH_PHASE=structured-command", exporter)
        self.assertIn("IO.eprintln", exporter)
        self.assertEqual(exporter.count("IO.println graph.compress"), 1)
        self.assertNotIn('IO.println "SOURCE_GRAPH_PHASE=', exporter)

    def test_unsupported_instructions_refuse_instead_of_falling_back(self):
        bad = query_graph()
        bad["command"]["first"] = {"kind": "host_count_oracle"}
        with self.assertRaises(ValueError):
            validate_query_source(serialized(bad), BLOB)


if __name__ == "__main__":
    unittest.main()
