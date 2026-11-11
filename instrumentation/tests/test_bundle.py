"""Portable capture archives remain verifiable independently of Lean installation."""
from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from bundle import pack, read_bundle, unpack
from capture import SCHEMA, STAGES, canonical, digest, validate


class BundleTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.out = self.base / "captures"
        self.out.mkdir()
        self.archive = self.base / "capture.zip"
        self.name = "native-high"
        lines = [f"{kind}|{case}|1|0|0|0|0" for kind in ("branch", "initialize")
                 for case in ("empty", "zero", "one", "mixed", "alternate", "all")]
        self.raw = ("\n".join(lines) + "\n").encode()
        gz = gzip.compress(self.raw, mtime=0)
        record = {"schema": SCHEMA, "name": self.name, "exit_code": 0,
                  "fingerprint": "a" * 64, "stdout_sha256": digest(self.raw),
                  "stdout_gzip_sha256": digest(gz), "stderr_sha256": digest(b""),
                  "coverage": validate(STAGES[self.name], self.raw), "machine_metrics": None}
        self.record = record
        runs = self.out / "runs"
        runs.mkdir()
        (runs / f"{self.name}.json").write_bytes(canonical(record))
        (runs / f"{self.name}.stdout.gz").write_bytes(gz)
        (runs / f"{self.name}.stderr").write_bytes(b"")
        (self.out / "index.json").write_bytes(canonical({"schema": SCHEMA, "completed": {self.name: record}}))

    def test_round_trip_and_repeatable_bytes(self):
        self.assertEqual(pack(self.out, self.archive), [self.name])
        first = self.archive.read_bytes()
        self.assertEqual(read_bundle(self.archive)[1], [self.name])
        pack(self.out, self.archive)
        self.assertEqual(first, self.archive.read_bytes())
        restore = self.base / "restored"
        self.assertEqual(unpack(self.archive, restore), [self.name])
        self.assertEqual((restore / "runs" / f"{self.name}.stdout.gz").read_bytes(),
                         (self.out / "runs" / f"{self.name}.stdout.gz").read_bytes())
        with self.assertRaises(ValueError):
            unpack(self.archive, restore)

    def test_reject_unfinished_trace(self):
        missing = self.out / "runs" / f"{self.name}.stdout.gz"
        missing.unlink()
        with self.assertRaises(ValueError):
            pack(self.out, self.archive)
        self.assertFalse(self.archive.exists())

    def test_reject_corrupt_input_even_with_success_record(self):
        stream = self.out / "runs" / f"{self.name}.stdout.gz"
        stream.write_bytes(gzip.compress(self.raw[:-4], mtime=0))
        with self.assertRaises(ValueError):
            pack(self.out, self.archive)

    def test_reject_duplicate_or_escaping_zip_path(self):
        pack(self.out, self.archive)
        with zipfile.ZipFile(self.archive, mode="a") as z:
            z.writestr("../escape.txt", "intruder")
        with self.assertRaises(ValueError):
            read_bundle(self.archive)

    def test_reject_missing_index_entry(self):
        (self.out / "index.json").write_bytes(canonical({"schema": SCHEMA, "completed": {}}))
        with self.assertRaises(ValueError):
            pack(self.out, self.archive)

    def test_reject_overwrite_in_capture_tree(self):
        with self.assertRaises(ValueError):
            pack(self.out, self.out / "bundle.zip")


if __name__ == "__main__":
    unittest.main()
