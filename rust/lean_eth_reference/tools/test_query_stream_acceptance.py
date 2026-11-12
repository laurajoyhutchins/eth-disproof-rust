"""Fail-closed contracts for compiling the original, four-stage query command."""
import json
import unittest

from query_stream_acceptance import (
    DECLARATION, IDENTIFIER, validate_query_source, generate_rust_query_test,
)

SOURCE_SHA = "4eaee87548250b2682affda7d05d947c05554bae"
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

    def test_unsupported_instructions_refuse_instead_of_falling_back(self):
        bad = query_graph()
        bad["command"]["first"] = {"kind": "host_count_oracle"}
        with self.assertRaises(ValueError):
            validate_query_source(serialized(bad), BLOB)


if __name__ == "__main__":
    unittest.main()
