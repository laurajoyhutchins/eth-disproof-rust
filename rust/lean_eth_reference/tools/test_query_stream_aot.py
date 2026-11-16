"""Offline fail-closed contracts for the *original* QueryStream AOT probe."""
import hashlib
import json
import os
import signal
import sys
import tempfile
from pathlib import Path
import time
import unittest

from query_stream_aot import (validate_query, run_bounded, verify_query_import_receipt,
                              record_query_refusal, source_export_phase,
                              ResourceLimitError, OutputLimitError, MAX_PROCESS_OUTPUT_BYTES,
                              MODULE, SOURCE_COMMIT, DECLARATION, IDENTIFIER)

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

    def test_pinned_full_query_receipt_checks_exact_olean_bytes(self):
        with tempfile.TemporaryDirectory(prefix="original-query-receipt-") as p:
            root = Path(p)
            artifact = root / ".lake/build/lib/lean" / Path(
                MODULE.replace(".", "/") + ".olean")
            artifact.parent.mkdir(parents=True)
            artifact.write_bytes(b"original-source-lean-olean-test-fixture")
            pin = {
                "mathlib_commit": "d13f23b723b8a846827a245b89c10fc7d3f11612",
                "lean": "Lean (version 4.34.1, fixture)",
            }
            good = {
                "status": "PINNED_ORIGINAL_LEAN_IMPORT_VERIFIED",
                "stage": "query", "module": MODULE,
                "source_commit": SOURCE_COMMIT,
                "source_git_blob": BLOB,
                "mathlib_commit": pin["mathlib_commit"],
                "lean_toolchain": "leanprover/lean4:v4.34.1",
                "lean_version": pin["lean"],
                "module_olean_sha256": hashlib.sha256(artifact.read_bytes()).hexdigest(),
                "query_stream_executable": False,
                "source_graph_compiled": False,
                "independent_lean_rust_parity": False,
                "math_or_resource_theorem": False,
            }
            receipt = root / "stage.receipt.json"
            receipt.write_text(json.dumps(good))
            verify_query_import_receipt(receipt, root, BLOB, pin)
            for key, bad in [
                    ("stage", "signature"),
                    ("module", MODULE + ".Substituted"),
                    ("source_commit", "0" * 40),
                    ("source_git_blob", "0" * 40),
                    ("mathlib_commit", "0" * 40),
                    ("module_olean_sha256", "0" * 64),
                    ("query_stream_executable", True)]:
                with self.subTest(field=key):
                    altered = dict(good)
                    altered[key] = bad
                    receipt.write_text(json.dumps(altered))
                    with self.assertRaisesRegex(ValueError, "mismatch|differ"):
                        verify_query_import_receipt(receipt, root, BLOB, pin)
            receipt.write_text(json.dumps(good))
            artifact.write_bytes(b"mutated module bytes")
            with self.assertRaisesRegex(ValueError, "bytes differ"):
                verify_query_import_receipt(receipt, root, BLOB, pin)

    def test_receipt_rejects_duplicate_json_fields(self):
        with tempfile.TemporaryDirectory(prefix="original-query-duplicate-") as p:
            receipt = Path(p) / "receipt.json"
            receipt.write_text('{"status":"good","status":"forged"}')
            with self.assertRaisesRegex(ValueError, "duplicate"):
                verify_query_import_receipt(receipt, Path(p), BLOB, {
                    "mathlib_commit": "any", "lean": "any",
                })

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

    @unittest.skipUnless(sys.platform.startswith("linux"), "POSIX supervision test")
    def test_detached_grandchild_cannot_hold_a_pipe_open_past_timeout(self):
        with tempfile.TemporaryDirectory(prefix="query-aot-detached-") as path:
            root = Path(path)
            pid_path = root / "detached.pid"
            child = "import time; time.sleep(8)"
            script = (
                "import pathlib,subprocess,sys,time\n"
                f"child=subprocess.Popen([sys.executable, '-c', {child!r}], "
                "start_new_session=True, stdout=sys.stdout, stderr=sys.stderr)\n"
                f"pathlib.Path({str(pid_path)!r}).write_text(str(child.pid))\n"
                "print('DETACHED_MARKER',flush=True)\n"
                "time.sleep(8)\n"
            )
            start = time.monotonic()
            try:
                with self.assertRaisesRegex(TimeoutError, "timeout 1s"):
                    run_bounded([sys.executable, "-c", script], root, 1,
                                log_base=root / "captured")
            finally:
                if pid_path.exists():
                    pid = int(pid_path.read_text())
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            self.assertLess(time.monotonic() - start, 5,
                            "supervisor blocked on a detached inherited pipe")
            self.assertIn("DETACHED_MARKER",
                          (root / "captured.stdout.log").read_text())

    @unittest.skipUnless(sys.platform.startswith("linux"), "POSIX supervision test")
    def test_oversized_output_is_refused_without_collecting_into_memory(self):
        with tempfile.TemporaryDirectory(prefix="query-aot-overoutput-") as path:
            root = Path(path)
            script = (f"import os; os.write(1, b'X'*"
                      f"({MAX_PROCESS_OUTPUT_BYTES}+100000))")
            start = time.monotonic()
            with self.assertRaisesRegex(OutputLimitError, "bounded output exceeded"):
                run_bounded([sys.executable, "-c", script], root, 20,
                            log_base=root / "large")
            self.assertLess(time.monotonic() - start, 6)
            self.assertGreater((root / "large.stdout.log").stat().st_size,
                               MAX_PROCESS_OUTPUT_BYTES)

    @unittest.skipUnless(sys.platform.startswith("linux"), "Linux RSS accounting")
    def test_process_group_rss_refuses_with_retained_diagnostics(self):
        with tempfile.TemporaryDirectory(prefix="query-aot-rss-") as path:
            root = Path(path)
            script = ("import time\\n"
                      "data = bytearray(64 * 1024 * 1024)\\n"
                      "for i in range(0, len(data), 4096): data[i] = 1\\n"
                      "print('ALLOCATED', flush=True)\\n"
                      "time.sleep(10)\\n")
            with self.assertRaisesRegex(ResourceLimitError, "RSS budget exceeded"):
                run_bounded([sys.executable, "-c", script], root, 6,
                            log_base=root / "original-command",
                            rss_limit_bytes=32 * 1024 * 1024)
            self.assertIn("ALLOCATED", (root / "original-command.stdout.log").read_text())

    def test_resource_refusal_records_exact_last_phase_without_success(self):
        with tempfile.TemporaryDirectory(prefix="query-aot-refusal-") as path:
            root = Path(path)
            stderr = root / "original-command.stderr.log"
            self.assertEqual(source_export_phase(stderr), "import-or-initialization")
            stderr.write_text("SOURCE_GRAPH_PHASE=source-identity-checked\\n"
                              "SOURCE_GRAPH_PHASE=decode-original-structured-command\\n")
            phase = source_export_phase(stderr)
            self.assertEqual(phase, "decode-original-structured-command")
            record_query_refusal(root, "original-command-export-resource-limit",
                                 "RSS budget exceeded: observed 123", phase)
            report = json.loads((root / "report.json").read_text())
            self.assertEqual(report, {
                "status": "REFUSED",
                "stage": "original-command-export-resource-limit",
                "reason": "RSS budget exceeded: observed 123",
                "source_phase": "decode-original-structured-command",
            })
            self.assertFalse((root / "query-stream.receipt.json").exists())

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
