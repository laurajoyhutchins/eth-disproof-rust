"""Offline regression tests for the resumable original Lean-to-Rust driver."""
import hashlib
import json
from pathlib import Path
import sys
import shutil
import tempfile
import unittest
from unittest.mock import patch

from lean_rust import identity, resolve, valid_cached, execute
from export_compiled_batch import (
    SOURCE_SHA, MATHLIB_SHA, atomic_write, export_batch, exporter_fingerprint,
    verified_receipt,
)

REC = {
    "id": "example_0",
    "module": "OAI.Algorithms.SubexponentialSAT.Example",
    "fqn": "OAI.Algorithms.SubexponentialSAT.Example.program",
    "git_blob": "a" * 40,
}
PINS = {
    "source_commit": SOURCE_SHA,
    "mathlib_commit": MATHLIB_SHA,
    "lean": "Lean (version 4.34.1, x86_64-linux-gnu)",
}


def write_receipt(folder: Path, record: dict = REC, pins: dict = PINS) -> dict:
    """Synthesize a table for validation tests, never as actual Lean evidence."""
    name = record["id"]
    raw = (f"PIN|{name}|{SOURCE_SHA}|{record['git_blob']}\n"
           f"PROGRAM|{name}|1|1|1|0|0|0\n"
           f"CODE|{name}|0|halt\n"
           f"END|{name}|1\n").encode("ascii")
    receipt = {
        "id": name, "module": record["module"], "declaration": record["fqn"],
        "abi": {"registers": 1, "stacks": 1, "labels": 1,
                "entry": 0, "input": 0, "output": 0},
        "source_commit": SOURCE_SHA, "source_git_blob": record["git_blob"],
        "status": "EXPORTED_FROM_PINNED_LEAN",
        "pins": pins, "exporter_sha256": exporter_fingerprint(),
        "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw),
    }
    (folder / (name + ".table")).write_bytes(raw)
    atomic_write(folder / (name + ".receipt.json"),
                 json.dumps(receipt, sort_keys=True) + "\n")
    return receipt


class DriverTests(unittest.TestCase):
    def test_identity_is_stable_and_source_sensitive(self):
        self.assertEqual(identity(REC), identity(dict(REC)))
        self.assertNotEqual(identity(REC), identity({**REC, "git_blob": "b" * 40}))

    def test_selector_must_be_unique(self):
        self.assertEqual(resolve([REC], REC["id"]), REC)
        with self.assertRaises(ValueError):
            resolve([REC, REC], REC["id"])
        with self.assertRaises(ValueError):
            resolve([REC], "missing")

    def test_failure_bundle_preserves_output_and_exit_code(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            with self.assertRaises(RuntimeError):
                execute([sys.executable, "-c", "print('DIAGNOSTIC'); raise SystemExit(7)"],
                        stage="test", folder=folder)
            report = json.loads((folder / "test.json").read_text())
            self.assertEqual(report["exit_code"], 7)
            self.assertIn("DIAGNOSTIC", (folder / "test.log").read_text())
            self.assertEqual(report["command"][0], sys.executable)

    def test_cached_receipt_requires_exact_abi_source_and_exporter(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            self.assertFalse(valid_cached(folder, REC))
            receipt = write_receipt(folder)
            batch = {"kind": "original-source-program-export",
                     "exported": [receipt], "pins": PINS}
            atomic_write(folder / "batch-report.json",
                         json.dumps(batch, sort_keys=True) + "\n")
            self.assertTrue(valid_cached(folder, REC))
            self.assertIsNotNone(verified_receipt(folder, REC, 1, PINS))
            self.assertIsNone(verified_receipt(folder, REC, 0, PINS))

            corrupted = json.loads(json.dumps(receipt))
            corrupted["abi"]["labels"] = 2
            atomic_write(folder / "example_0.receipt.json", json.dumps(corrupted))
            self.assertFalse(valid_cached(folder, REC))
            atomic_write(folder / "example_0.receipt.json", json.dumps(receipt))
            self.assertTrue(valid_cached(folder, REC))

            with patch("export_compiled_batch.LEAN_EXPORTER", folder / "changed.lean"):
                (folder / "changed.lean").write_text("changed exporter")
                self.assertFalse(valid_cached(folder, REC))
            self.assertTrue(valid_cached(folder, REC))

            (folder / "example_0.table").write_bytes(b"tampered")
            self.assertFalse(valid_cached(folder, REC))
            write_receipt(folder)
            batch["pins"] = {**PINS, "mathlib_commit": "b" * 40}
            atomic_write(folder / "batch-report.json", json.dumps(batch))
            self.assertFalse(valid_cached(folder, REC))

    def test_interrupted_batch_checkpoints_and_resumes_valid_receipts(self):
        second = {**REC, "id": "example_1",
                  "fqn": "OAI.Algorithms.SubexponentialSAT.Example.another"}
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            calls = []

            def export(rec, *_args):
                calls.append(rec["id"])
                if len(calls) == 2:
                    raise KeyboardInterrupt()
                return write_receipt(folder, rec)

            with patch("export_compiled_batch.export_one", side_effect=export):
                with self.assertRaises(KeyboardInterrupt):
                    export_batch([REC, second], folder, folder, PINS, 10, 2, False)
            partial = json.loads((folder / "batch-report.json").read_text())
            self.assertEqual(partial["state"], "in_progress")
            self.assertEqual(partial["attempted"], 1)
            self.assertEqual([x["id"] for x in partial["exported"]], [REC["id"]])

            calls.clear()
            with patch("export_compiled_batch.export_one", side_effect=export):
                result = export_batch([REC, second], folder, folder, PINS, 10, 2, False)
            self.assertEqual(calls, [second["id"]])
            self.assertEqual(len(result["exported"]), 2)
            final = json.loads((folder / "batch-report.json").read_text())
            self.assertEqual(final["state"], "complete")
            self.assertEqual(final["attempted"], 2)
            self.assertEqual(len(final["exported"]), 2)

    def test_restored_remote_snapshot_reuses_only_validated_individual_exports(self):
        """A fresh runner may restore files, but never trust them without validation."""
        with tempfile.TemporaryDirectory() as temp:
            first = Path(temp) / "first-github-run"
            second = Path(temp) / "second-github-run"
            first.mkdir()
            receipt = write_receipt(first)
            atomic_write(first / "batch-report.json",
                         json.dumps({"kind": "original-source-program-export",
                                     "pins": PINS, "exported": [receipt]}) + "\n")
            shutil.copytree(first, second)
            with patch("export_compiled_batch.export_one") as compiler:
                result = export_batch([REC], second, second, PINS, 10, 2, False)
            compiler.assert_not_called()
            self.assertEqual([row["id"] for row in result["exported"]], [REC["id"]])

            # A corrupted restore is re-exported rather than accepted or marked verified.
            (second / "example_0.table").write_bytes(b"bad-cache-bytes")
            with patch("export_compiled_batch.export_one",
                       side_effect=lambda rec, *_: write_receipt(second, rec)) as compiler:
                result = export_batch([REC], second, second, PINS, 10, 2, False)
            compiler.assert_called_once()
            self.assertEqual(len(result["exported"]), 1)

            # A previous exported table under an old implementation is also stale.
            with tempfile.TemporaryDirectory() as changed:
                fake_exporter = Path(changed) / "changed-exporter.lean"
                fake_exporter.write_text("changed implementation")
                with patch("export_compiled_batch.LEAN_EXPORTER", fake_exporter):
                    with patch("export_compiled_batch.export_one",
                               side_effect=lambda rec, *_: write_receipt(second, rec)) as compiler:
                        export_batch([REC], second, second, PINS, 10, 2, False)
                    compiler.assert_called_once()

    def test_exporter_receipt_is_not_parity_evidence(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            receipt = write_receipt(folder)
            self.assertEqual(receipt["status"], "EXPORTED_FROM_PINNED_LEAN")
            self.assertNotIn("parity", receipt)
            self.assertNotIn("verified_differential", receipt)


if __name__ == "__main__":
    unittest.main()
