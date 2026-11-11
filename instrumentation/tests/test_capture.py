"""No Lean or network is required for runner and corruption-regression tests."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import capture as cap


class CaptureTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "instrumentation/probes").mkdir(parents=True)
        (self.root / "instrumentation/probes/sample.lean").write_text("-- fake probe")
        self.stage = cap.Stage("sample.lean", "machine", ("empty",), ("branch",))
        self.env = {"original_commit": cap.PIN, "lean_version": "4.34.1"}
        self.trace = ("PROGRAM|empty|2|2|2|0|0|1\n"
                      "CODE|empty|0|goto:1\n"
                      "CODE|empty|1|halt\n"
                      "INITIAL|empty|0|00|\n"
                      "STEP|empty|0|0|goto:1|1|00|\n"
                      "STEP|empty|1|1|halt|-|00|\n"
                      "END|empty|halted|2|-|00|\n").encode()
        self.patchers = [mock.patch.object(cap, "ROOT", self.root),
                         mock.patch.object(cap, "STAGES", {"sample": self.stage}),
                         mock.patch.object(cap, "LEAN_ROOT", self.root)]
        for p in self.patchers:
            p.start()
            self.addCleanup(p.stop)

    def test_complete_machine(self):
        coverage = cap.validate(self.stage, self.trace)
        self.assertEqual(coverage["cases"], ["empty"])
        self.assertEqual(coverage["lines"], 7)

    def test_reject_nonterminating_and_partial_trace(self):
        for broken in (self.trace.replace(b"halted", b"fuel_exhausted"),
                       self.trace.replace(b"CODE|empty|1|halt\n", b""),
                       self.trace.replace(b"STEP|empty|1", b"STEP|empty|8"),
                       self.trace.replace(b"END|empty|halted|2|-|00|\n", b""),
                       self.trace + b"END|empty|halted|2|-|00|\n"):
            with self.subTest(broken=broken[-100:]), self.assertRaises(ValueError):
                cap.validate(self.stage, broken)

    def test_legacy_requires_all_unique_cases(self):
        stage = cap.Stage("sample.lean", "legacy", ("branch/empty", "branch/one"))
        self.assertEqual(len(cap.validate(stage, b"branch|empty|1|0\nbranch|one|2|1\n")["cases"]), 2)
        for broken in (b"branch|empty|1|0\n", b"branch|empty|1|0\nbranch|empty|2|1\n",
                       b"branch|empty|1|0\nbranch|one|bad|1\n"):
            with self.assertRaises(ValueError):
                cap.validate(stage, broken)

    def test_capture_resume_integrity_and_replace(self):
        out = self.root / "out"
        ok = subprocess.CompletedProcess(args=[], returncode=0, stdout=self.trace, stderr=b"")
        with mock.patch.object(cap, "process", return_value=ok) as runner:
            cap.capture(out, ["sample"], self.env, 1000, False)
            cap.capture(out, ["sample"], self.env, 1000, False)
            self.assertEqual(runner.call_count, 1, "resume should not rerun a complete Lean stage")
            self.assertIsNotNone(cap.check_record(out, "sample", cap.stage_fingerprint("sample", self.env, 1000)))
            with self.assertRaises(ValueError):
                cap.capture(out, ["sample"], self.env, 2000, False)
            cap.capture(out, ["sample"], self.env, 2000, True)
            self.assertEqual(runner.call_count, 2)
        data = out / "runs/sample.stdout.gz"
        data.write_bytes(data.read_bytes() + b"tampered")
        with self.assertRaises(ValueError):
            cap.check_record(out, "sample", cap.stage_fingerprint("sample", self.env, 2000))

    def test_failed_process_never_creates_success_marker(self):
        out = self.root / "out"
        bad = subprocess.CompletedProcess(args=[], returncode=1, stdout=b"", stderr=b"missing Mathlib")
        with mock.patch.object(cap, "process", return_value=bad):
            with self.assertRaises(RuntimeError):
                cap.capture(out, ["sample"], self.env, 1000, False)
        self.assertFalse((out / "runs/sample.json").exists())
        self.assertEqual((out / "runs/sample.failed.stderr").read_bytes(), b"missing Mathlib")


if __name__ == "__main__":
    unittest.main()
