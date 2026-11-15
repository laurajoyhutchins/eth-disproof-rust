"""Cheap TDD checks for the original Lean -> one Rust counting executable seam."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

from temporary_rust_crate import isolated_cargo_manifest

from compile_native_count import (
    FQN, IDENTITY, INPUT, OUTPUT, LARGE_FQN, LARGE_IDENTITY, MODULE,
    SOURCE_SHA, compile_counting, inspect_graph, large_only_wrapper, lean_wrapper, rust_binary,
)

BLOB = "a" * 40


def graph(command, labels=2, input_stack=INPUT, output_stack=OUTPUT,
          mode='full'):
    fqn, identity = (FQN, IDENTITY) if mode == 'full' else (LARGE_FQN, LARGE_IDENTITY)
    return (json.dumps({
        "kind": "original-structured-source-v1",
        "source_commit": SOURCE_SHA,
        "source_blob": BLOB,
        "declaration": fqn,
        "id": identity,
        "abi": {"r": 80, "s": 1220, "labels": labels,
                "input": input_stack, "output": output_stack},
        "command": command,
    }, separators=(",", ":")) + "\n").encode("ascii")


class WholeCountingCompilationTests(unittest.TestCase):
    def test_exact_source_wiring_cannot_become_host_oracle(self):
        source = lean_wrapper(3, 20)
        self.assertIn("Native.entryCommand 20", source)
        self.assertIn("Native.outerCommand 3 (NativeLeafProgram.command 3)", source)
        self.assertIn("ABI.countStack ABI.answerStack", source)
        self.assertIn("StructuredCalls", source)
        self.assertNotIn("SAT.count", source)
        self.assertEqual(lean_wrapper(3, 20), source)

    def test_large_domain_retains_original_cutoff_and_runnable_branch(self):
        source = large_only_wrapper(3, 20)
        program = source.split("-- This is a data-state refinement", 1)[0]
        self.assertIn("Native.frontendCommand", program)
        self.assertIn("FiniteFallback.cutoffCommand 20", program)
        self.assertIn(".ite 75 (.base .skip)", program)
        self.assertIn("Native.outerCommand 3 (NativeLeafProgram.command 3)", program)
        self.assertNotIn("FiniteFallback.framedCommand", program)
        self.assertNotIn("SAT.count", program)
        # Conditional Lean source theorem, not a host assumption of global
        # equivalence: original false-cutoff branch runs the same state effect.
        self.assertIn("largeOnlyBranch_execution_eq_original", source)
        self.assertIn("hfalse : c.regs 75 = false", source)
        self.assertIn("Native.entryCommand B large", source)
        self.assertIn("FiniteFallback.framedCommand B", source)

        raw = graph({"kind": "atom", "opcode": "set:0:1"},
                    mode="large-domain")
        _, root = inspect_graph(raw, BLOB, mode="large-domain")
        generated = rust_binary(BLOB, __import__("hashlib").sha256(raw).hexdigest(), mode="large-domain")
        self.assertIn("status=physical-large-domain-count-complete", generated)
        self.assertIn("if cnf.variables() <= 20 {", generated)
        self.assertNotIn("count_terminal(", generated)
        with self.assertRaises(ValueError):
            inspect_graph(raw, BLOB, mode="full")
        with self.assertRaises(ValueError):
            inspect_graph(graph({"kind": "skip"}, labels=1),
                          BLOB, mode="large-domain")
        with self.assertRaises(ValueError):
            rust_binary(BLOB, __import__("hashlib").sha256(raw).hexdigest(), mode="oracle")

    def test_reject_invalid_parameters(self):
        for k, cutoff in [(1, 20), (9, 20), (3, -1), (3, 129)]:
            with self.subTest(k=k, cutoff=cutoff):
                with self.assertRaises(ValueError):
                    lean_wrapper(k, cutoff)
                with self.assertRaises(ValueError):
                    large_only_wrapper(k, cutoff)

    def test_full_machine_abi_and_synthetic_instruction_graph(self):
        g, root = inspect_graph(
            graph({"kind": "atom", "opcode": "set:0:1"}), BLOB
        )
        self.assertEqual(g["abi"]["labels"], 2)
        raw = graph({"kind": "atom", "opcode": "set:0:1"})
        digest = __import__("hashlib").sha256(raw).hexdigest()
        compiled = rust_binary(BLOB, digest)
        self.assertIn('DeferredProgram::from_original_source_json(include_bytes!("count.graph.json")', compiled)
        self.assertIn("SourceGraphBinding", compiled)
        self.assertNotIn("Block::call(", compiled)
        self.assertIn("program.run(&mut state, limits)", compiled)
        self.assertIn("state.stacks[256]", compiled)
        self.assertIn("state.stacks[1216]", compiled)
        self.assertIn("count_word_decimal", compiled)
        self.assertIn("source_instructions=", compiled)
        self.assertIn("clause.literals().len() > 3", compiled)
        self.assertIn("formula exceeds compiled clause-width bound", compiled)
        self.assertIn("if cnf.variables() <= 20 {", compiled)
        self.assertIn("unsupported noncomputable finite fallback: n <= 20", compiled)
        # Parameter-specific refusal is compiled into the executable. A
        # selected cutoff is not asserted to be the original theorem cutoff.
        variant = rust_binary(BLOB, digest, width=3, cutoff=2)
        self.assertIn("if cnf.variables() <= 2 {", variant)
        self.assertNotIn("n <= 20", variant)
        self.assertNotIn("count_terminal(", compiled)
        self.assertNotIn(".count_sat(", compiled)

    def test_reused_exact_graph_skips_lean_build_and_refuses_wrong_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            upstream = root / "upstream"
            lake = root / "lake"
            rust_crate = Path(__file__).resolve().parents[1]
            source = upstream / "lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeOuter.lean"
            source.parent.mkdir(parents=True)
            source.write_text("-- pinned test fixture\n")
            lake.mkdir()
            preexport = root / "source.graph.json"
            preexport.write_bytes(graph({"kind": "atom", "opcode": "set:0:1"},
                                        mode="large-domain"))
            a = SimpleNamespace(upstream=upstream, lake_root=lake,
                                rust_crate=rust_crate, output_dir=root/"out",
                                width=3, cutoff=20, timeout_seconds=120,
                                require_certificate=False, entry_mode="large-domain",
                                source_graph=preexport)
            calls = []
            def cargo_only(args, **kwargs):
                calls.append(args)
                if args[0] != "cargo":
                    raise AssertionError("reused graph must not rebuild original Lean")
                binary = Path(args[args.index("--manifest-path") + 1]).parent / "target/release/eth_native_count"
                binary.parent.mkdir(parents=True)
                binary.write_bytes(b"stub-generated-executable")
                return ""
            with patch('compile_native_count.ensure_pinned', return_value={}), \
                 patch('compile_native_count.blob_hash', return_value=BLOB), \
                 patch('compile_native_count.run_command', side_effect=cargo_only):
                result = compile_counting(a)
            self.assertEqual(result["entry_mode"], "large-domain")
            self.assertEqual(result["rust_loader"], "original-structured-source-v1/serde-native")
            self.assertEqual(result["source_graph_sha256"],
                             __import__("hashlib").sha256(preexport.read_bytes()).hexdigest())
            self.assertEqual(len(calls), 1)
            self.assertEqual(calls[0][0], "cargo")
            self.assertTrue((a.output_dir/"count.receipt.json").is_file())
            # The exact same bytes cannot be mistaken for the canonical
            # complete-source declaration or for a graph from a wrong commit.
            a.entry_mode = 'full'
            with patch('compile_native_count.ensure_pinned', return_value={}), \
                 patch('compile_native_count.blob_hash', return_value=BLOB), \
                 patch('compile_native_count.run_command', side_effect=cargo_only):
                with self.assertRaises(ValueError):
                    compile_counting(a)
            self.assertFalse((a.output_dir/"count.receipt.json").exists())
            self.assertEqual(len(calls), 1)
    def test_codegen_refuses_unsafe_cutoffs(self):
        _, root = inspect_graph(graph({"kind": "skip"}, labels=1), BLOB)
        for width, cutoff in [(1, 20), (9, 20), (3, -1), (3, 129)]:
            with self.subTest(width=width, cutoff=cutoff):
                with self.assertRaises(ValueError):
                    rust_binary(BLOB, __import__("hashlib").sha256(graph({"kind": "skip"}, labels=1)).hexdigest(),
                                width=width, cutoff=cutoff)

    def test_bad_abi_or_identity_must_refuse(self):
        tampered = [
            graph({"kind": "skip"}, labels=1, input_stack=257),
            graph({"kind": "skip"}, labels=1, output_stack=1217),
            graph({"kind": "skip"}, labels=3),
            graph({"kind": "oracle"}, labels=2),
            graph({"kind": "atom", "opcode": "set:80:1"}),
            graph({"kind": "while", "test":80, "body": {"kind": "skip"}}),
            graph({"kind": "skip"}, labels=1).replace(BLOB.encode(), b"b" * 40),
            graph({"kind": "skip"}, labels=1).replace(FQN.encode(), b"FakeProgram"),
        ]
        for bad in tampered:
            with self.subTest(payload=bad[:80]):
                with self.assertRaises((ValueError, KeyError)):
                    inspect_graph(bad, BLOB)

    @unittest.skipUnless(shutil.which("cargo"), "Rust toolchain not available")
    def test_generated_entrypoint_compiles_and_exposes_help(self):
        # Compile emitted Rust, rather than merely checking generated text.
        # This is a small synthetic *codegen smoke*, not full source acceptance.
        raw = graph({"kind": "atom", "opcode": "set:0:1"})
        _, root = inspect_graph(raw, BLOB)
        rust_crate = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory(prefix="source-count-codegen-") as tmp:
            project = Path(tmp)
            (project / "src").mkdir()
            (project / "src" / "main.rs").write_text(
                rust_binary(BLOB, __import__("hashlib").sha256(raw).hexdigest()), encoding="utf-8")
            (project / "src" / "count.graph.json").write_bytes(raw)
            (project / "Cargo.toml").write_text(
                isolated_cargo_manifest("native_count_codegen_smoke", rust_crate),
                encoding="utf-8",
            )
            env = os.environ.copy()
            env.setdefault("CARGO_TARGET_DIR", str(rust_crate.parents[1] / "target"))
            result = subprocess.run(
                ["cargo", "run", "--offline", "--quiet", "--manifest-path",
                 str(project / "Cargo.toml"), "--", "--help"],
                cwd=project, env=env, text=True, capture_output=True, timeout=120,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("Usage: eth-count", result.stdout)

            # Exercise the emitted Rust binary itself, not only its text.
            # A nonterminal 3-variable formula below cutoff must refuse
            # before any synthetic or source machine graph can run.
            refused = subprocess.run(
                ["cargo", "run", "--offline", "--quiet", "--manifest-path",
                 str(project / "Cargo.toml"), "--"],
                input="p cnf 3 2\n1 2 0\n1 3 0\n",
                cwd=project, env=env, text=True, capture_output=True, timeout=120,
                check=False,
            )
            self.assertEqual(refused.returncode, 2, refused.stderr)
            self.assertEqual(refused.stdout, "")
            self.assertIn(
                "unsupported noncomputable finite fallback: n <= 20",
                refused.stderr,
            )

    def test_duplicate_keys_are_not_silently_accepted(self):
        source = graph({"kind": "skip"}, labels=1)
        duplicate = source.replace(b'"output":1216', b'"output":1216,"output":1216')
        with self.assertRaises(ValueError):
            inspect_graph(duplicate, BLOB)


if __name__ == "__main__":
    unittest.main()
