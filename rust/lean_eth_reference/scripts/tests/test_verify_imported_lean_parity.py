"""Offline, stdlib-only evidence-gate tests; no fake Lean traces as evidence."""
from __future__ import annotations

import importlib.util
from pathlib import Path
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "verify-imported-lean-parity.py"
spec = importlib.util.spec_from_file_location("verify_imported_lean_parity", SCRIPT)
assert spec is not None and spec.loader is not None
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class EvidenceGateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.name = "lean/OAI/Algorithms/SubexponentialSAT/BitProgram.lean"
        original = self.root / self.name
        original.parent.mkdir(parents=True)
        original.write_bytes(b"original pinned source\n")
        self.record = {
            "repository": "openai/math", "commit": module.SOURCE_COMMIT,
            "toolchain": "leanprover/lean4:v4.34.1",
            "files": {self.name: module.git_blob_sha(original.read_bytes())},
        }

    def test_accepts_matching_original_blob(self) -> None:
        self.assertEqual(module.validate_manifest(self.record, self.root), self.record["files"])

    def test_rejects_substituted_source(self) -> None:
        (self.root / self.name).write_text("a substitute Lean program\n")
        with self.assertRaisesRegex(ValueError, "does not match"):
            module.validate_manifest(self.record, self.root)

    def test_rejects_missing_source(self) -> None:
        (self.root / self.name).unlink()
        with self.assertRaisesRegex(ValueError, "missing"):
            module.validate_manifest(self.record, self.root)

    def test_rejects_wrong_commit_and_version(self) -> None:
        self.record["commit"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "wrong upstream"):
            module.validate_manifest(self.record, self.root)
        self.record["commit"] = module.SOURCE_COMMIT
        self.record["toolchain"] = "leanprover/lean4:v4.35.0"
        with self.assertRaisesRegex(ValueError, "wrong Lean"):
            module.validate_manifest(self.record, self.root)

    def test_rejects_traversal_and_empty_manifest(self) -> None:
        self.record["files"] = {self.name + "/../BitProgram.lean": "0" * 40}
        with self.assertRaisesRegex(ValueError, "invalid source"):
            module.validate_manifest(self.record, self.root)
        self.record["files"] = {}
        with self.assertRaisesRegex(ValueError, "must list"):
            module.validate_manifest(self.record, self.root)

    def test_requires_pinned_mathlib_dependency(self) -> None:
        lock = {"packages": [{
            "name": "mathlib",
            "type": "git",
            "url": "https://github.com/leanprover-community/mathlib4.git",
            "rev": module.MATHLIB_COMMIT,
        }]}
        module.verify_mathlib_lock(lock)
        lock["packages"][0]["rev"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "Mathlib lock"):
            module.verify_mathlib_lock(lock)
        with self.assertRaisesRegex(ValueError, "Mathlib lock"):
            module.verify_mathlib_lock({"packages": []})

    def test_has_five_distinct_source_exec_stages(self) -> None:
        self.assertEqual(len(module.STAGES), 5)
        self.assertEqual(len({row[0] for row in module.STAGES.values()}), 5)
        self.assertEqual(len({row[1] for row in module.STAGES.values()}), 5)
        self.assertEqual(len({row[2] for row in module.STAGES.values()}), 5)


if __name__ == "__main__":
    unittest.main()
