"""Cheap TDD checks for the original Lean -> one Rust counting executable seam."""
import json
import unittest

from compile_native_count import (
    FQN, IDENTITY, INPUT, OUTPUT, MODULE, SOURCE_SHA, inspect_graph,
    lean_wrapper, rust_binary,
)

BLOB = "a" * 40


def graph(command, labels=2, input_stack=INPUT, output_stack=OUTPUT):
    return (json.dumps({
        "kind": "original-structured-source-v1",
        "source_commit": SOURCE_SHA,
        "source_blob": BLOB,
        "declaration": FQN,
        "id": IDENTITY,
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

    def test_reject_invalid_parameters(self):
        for k, cutoff in [(1, 20), (9, 20), (3, -1), (3, 129)]:
            with self.subTest(k=k, cutoff=cutoff):
                with self.assertRaises(ValueError):
                    lean_wrapper(k, cutoff)

    def test_full_machine_abi_and_synthetic_instruction_graph(self):
        g, root = inspect_graph(
            graph({"kind": "atom", "opcode": "set:0:1"}), BLOB
        )
        self.assertEqual(g["abi"]["labels"], 2)
        compiled = rust_binary(root)
        self.assertIn("DeferredProgram::composed(256, 1216,", compiled)
        self.assertIn("program.run(&mut state, limits)", compiled)
        self.assertIn("state.stacks[256]", compiled)
        self.assertIn("state.stacks[1216]", compiled)
        self.assertIn("count_word_decimal", compiled)
        self.assertIn("source_instructions=", compiled)
        self.assertIn("clause.literals().len() > 3", compiled)
        self.assertIn("formula exceeds compiled clause-width bound", compiled)
        self.assertNotIn("count_terminal(", compiled)
        self.assertNotIn(".count_sat(", compiled)

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

    def test_duplicate_keys_are_not_silently_accepted(self):
        source = graph({"kind": "skip"}, labels=1)
        duplicate = source.replace(b'"output":1216', b'"output":1216,"output":1216')
        with self.assertRaises(ValueError):
            inspect_graph(duplicate, BLOB)


if __name__ == "__main__":
    unittest.main()
