"""Acceptance tests for closed original computational-expression exports."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from validate_computation import PINS, make_view, read_computation


def records():
    return [
        {
            "kind": "manifest", "protocol": "original-computational-expr-v1",
            "source": "openai", "module": "Smoke", "roots": ["Root"],
            "complete": False, "semantics": "elaborated-source",
        },
        {
            "kind": "declaration", "id": "Root", "defining_module": "Smoke",
            "declaration_kind": "definition", "body_available": True,
            "project_refs": ["Helper"], "external_refs": ["Nat.succ"],
            "operators": [{
                "path": "0", "operator": "StructuredCalls.Cmd.seq",
                "control_kind": "sequence", "arity": 2,
                "argument_heads": ["Helper", None],
                "operand_effects": {"reg_reads_arg_positions": [], "reg_writes_arg_positions": [],
                                    "stack_reads_arg_positions": [], "stack_writes_arg_positions": []},
            }],
        },
        {
            "kind": "declaration", "id": "Helper", "defining_module": "Smoke",
            "declaration_kind": "definition", "body_available": True,
            "project_refs": [], "external_refs": [],
            "operators": [],
        },
        {"kind": "complete", "nodes": 2, "operators": 1,
         "roots": ["Root"]},
    ]


class ExportValidationTests(unittest.TestCase):
    def with_file(self, rows, test):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "graph.jsonl"
            path.write_text("".join(json.dumps(x) + "\n" for x in rows))
            return test(path)

    def test_closed_source_projection(self):
        def check(path):
            source, mathlib, lean = PINS["openai"]
            v = make_view(path, source, mathlib, lean)
            self.assertTrue(v["raw_complete"])
            self.assertEqual(v["counts"]["declarations"], 2)
            self.assertEqual(v["counts"]["operator_occurrences"], 1)
            self.assertEqual(v["counts"]["project_reference_edges"], 1)
            self.assertEqual(v["counts"]["external_reference_occurrences"], 1)
            self.assertEqual(v["edges"][0]["kind"], "elaborated-value-reference")
            self.assertEqual(v["operators"][0]["control_kind"], "sequence")
            self.assertEqual(len(v["nodes"]), 2)
        self.with_file(records(), check)

    def test_partial_refused(self):
        self.with_file(records()[:-1], lambda p:
            self.assertRaisesRegex(ValueError, "incomplete", read_computation, p))

    def test_missing_reference_refused(self):
        rows = records()
        rows.pop(2)
        rows[-1]["nodes"] = 1
        self.with_file(rows, lambda p:
            self.assertRaisesRegex(ValueError, "unresolved", read_computation, p))

    def test_duplicate_operator_refused(self):
        rows = records()
        rows[1]["operators"].append(dict(rows[1]["operators"][0]))
        rows[-1]["operators"] = 2
        self.with_file(rows, lambda p:
            self.assertRaisesRegex(ValueError, "duplicate", read_computation, p))

    def test_wrong_pin_refused(self):
        self.with_file(records(), lambda p:
            self.assertRaisesRegex(ValueError, "pin mismatch", make_view,
                                   p, "0"*40, PINS["openai"][1],
                                   PINS["openai"][2]))

    def test_bad_operator_head_count_refused(self):
        rows = records()
        rows[1]["operators"][0]["argument_heads"] = ["Helper"]
        self.with_file(rows, lambda p:
            self.assertRaisesRegex(ValueError, "argument heads", read_computation, p))

    def test_trailing_record_refused(self):
        rows = records()
        rows.append(rows[1])
        self.with_file(rows, lambda p:
            self.assertRaisesRegex(ValueError, "follow", read_computation, p))

    def test_boundary_has_no_fake_operators(self):
        rows = records()
        rows[1]["body_available"] = False
        self.with_file(rows, lambda p:
            self.assertRaisesRegex(ValueError, "without a body", read_computation, p))


if __name__ == "__main__":
    unittest.main()
