"""Offline fail-closed contracts for the *original* QueryStream AOT probe."""
import json
import sys
import tempfile
from pathlib import Path
import time
import unittest

from query_stream_aot import validate_query, run_bounded, SOURCE_COMMIT, DECLARATION, IDENTIFIER

BLOB = "f" * 40


def graph():
    return {
        "kind": "original-structured-source-v1",
        "source_commit": SOURCE_COMMIT,
        "source_blob": BLOB,
        "declaration": DECLARATION,
        "id": IDENTIFIER,
        "abi": {"r": 40, "s": 896, "labels": 4,
                "input": 330, "output": 323},
        "command": {
            "kind": "seq", "first": {"kind": "atom", "opcode": "set:0:1"},
            "second": {"kind": "seq",
                       "first": {"kind": "atom", "opcode": "set:1:1"},
                       "second": {"kind": "atom", "opcode": "set:2:1"}},
        },
    }


def raw(value):
    return (json.dumps(value, separators=(",", ":")) + "\n").encode("ascii")


class QueryAotContract(unittest.TestCase):
    def test_full_command_shape_and_original_physical_abi(self):
        command, abi = validate_query(raw(graph()), BLOB)
        self.assertEqual(abi, (40, 896, 4, 1, 330, 323))
        self.assertEqual(command.instr(1, 0, 1), ("set", (0, 1, 2)))
        self.assertEqual(command.instr(1, 0, 3), ("set", (2, 1, 0)))

    def test_missing_stage_refused(self):
        value = graph()
        value["command"] = value["command"]["first"]
        value["abi"]["labels"] = 2
        with self.assertRaisesRegex(ValueError, "high-query"):
            validate_query(raw(value), BLOB)

    def test_wrong_output_port_refused(self):
        value = graph()
        value["abi"]["output"] = 324
        with self.assertRaisesRegex(ValueError, "physical ABI"):
            validate_query(raw(value), BLOB)

    def test_missing_label_or_foreign_declaration_refused(self):
        for field, value in [("labels", 3), ("declaration", "Substituted.Oracle")]:
            item = graph()
            if field == "labels":
                item["abi"][field] = value
            else:
                item[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                validate_query(raw(item), BLOB)

    @unittest.skipUnless(sys.platform.startswith("linux"), "POSIX process-group test")
    def test_timeout_reaps_subprocess_tree_before_success_receipt(self):
        with tempfile.TemporaryDirectory(prefix="query-aot-reap-") as path:
            root = Path(path)
            marker = root / "unexpected-late-worker-output"
            # This parent forks a child that tries to publish late output after
            # the process group has timed out. A kill of the parent PID only
            # would let the child continue writing.
            child_code = (f"import time; time.sleep(1.6); "
                          f"open({str(marker)!r}, 'w').write('bad')")
            script = (f"import subprocess,sys,time\n"
                      f"subprocess.Popen([sys.executable, '-c', {child_code!r}])\n"
                      f"time.sleep(10)\n")
            with self.assertRaises(TimeoutError):
                run_bounded([sys.executable, "-c", script], root, 1)
            time.sleep(0.8)
            self.assertFalse(marker.exists(), "timed-out Lean descendant survived")

    def test_does_not_claim_kernel_certification_from_derived_digest(self):
        code = (Path(__file__).parent / "query_stream_aot.py").read_text()
        self.assertIn("SOURCE_GRAPH_NATIVE_AOT_UNCERTIFIED", code)
        self.assertIn('"kernel_certificate": False', code)
        self.assertIn('"independent_lean_physical_parity": False', code)
        self.assertIn('"correct_count_reconstruction": False', code)
        self.assertIn('"full_prepared_input_execution": False', code)
        self.assertIn('original-source-codegen', code)
        self.assertNotIn("SAT.count(", code)


if __name__ == "__main__":
    unittest.main()
