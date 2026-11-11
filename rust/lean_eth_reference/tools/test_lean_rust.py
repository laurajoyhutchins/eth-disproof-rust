"""Offline regression tests for the resumable Lean-to-Rust driver."""
import hashlib
import json
from pathlib import Path
import tempfile
import sys
import unittest
from lean_rust import identity, resolve, valid_cached, execute
from export_compiled_batch import SOURCE_SHA, MATHLIB_SHA

REC = {"id":"example_0","module":"OAI.Algorithms.SubexponentialSAT.Example","fqn":"OAI.Algorithms.SubexponentialSAT.Example.program",
       "git_blob":"a"*40}

class DriverTests(unittest.TestCase):
    def test_identity_is_stable_and_source_sensitive(self):
        self.assertEqual(identity(REC), identity(dict(REC)))
        self.assertNotEqual(identity(REC), identity({**REC, "git_blob":"b"*40}))

    def test_selector_must_be_unique(self):
        self.assertEqual(resolve([REC],REC["id"]),REC)
        with self.assertRaises(ValueError):
            resolve([REC,REC],REC["id"])
        with self.assertRaises(ValueError):
            resolve([REC],"missing")

    def test_failure_bundle_preserves_output_and_exit_code(self):
        with tempfile.TemporaryDirectory() as temp:
            folder=Path(temp)
            with self.assertRaises(RuntimeError):
                execute([sys.executable, "-c", "print('DIAGNOSTIC'); raise SystemExit(7)"],
                        stage="test", folder=folder)
            report=json.loads((folder/"test.json").read_text())
            self.assertEqual(report["exit_code"],7)
            self.assertIn("DIAGNOSTIC",(folder/"test.log").read_text())
            self.assertEqual(report["command"][0],sys.executable)

    def test_cached_receipt_requires_matching_original_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            folder=Path(temp)
            self.assertFalse(valid_cached(folder,REC))
            raw=(f"PIN|example_0|{SOURCE_SHA}|{REC['git_blob']}\n"
                 "PROGRAM|example_0|1|1|1|0|0|0\n"
                 "CODE|example_0|0|halt\n"
                 "END|example_0|1\n").encode("ascii")
            (folder/"example_0.table").write_bytes(raw)
            receipt={"id":REC["id"],"module":REC["module"],
                     "abi":{"registers":1,"stacks":1,"labels":1,"entry":0,"input":0,"output":0},
                     "source_commit":SOURCE_SHA,"source_git_blob":REC["git_blob"],
                     "declaration":REC["fqn"],"status":"EXPORTED_FROM_PINNED_LEAN",
                     "sha256":hashlib.sha256(raw).hexdigest(),"bytes":len(raw)}
            (folder/"example_0.receipt.json").write_text(json.dumps(receipt))
            batch={"kind":"original-source-program-export", "exported":[receipt],
                   "pins":{"source_commit":SOURCE_SHA, "mathlib_commit":MATHLIB_SHA,
                           "lean":"Lean (version 4.34.1, x86_64-linux-gnu)"}}
            (folder/"batch-report.json").write_text(json.dumps(batch))
            self.assertTrue(valid_cached(folder,REC))
            receipt["abi"]["labels"]=2
            (folder/"example_0.receipt.json").write_text(json.dumps(receipt))
            batch["exported"]=[receipt]
            (folder/"batch-report.json").write_text(json.dumps(batch))
            self.assertFalse(valid_cached(folder,REC))
            receipt["abi"]["labels"]=1
            (folder/"example_0.receipt.json").write_text(json.dumps(receipt))
            batch["exported"]=[receipt]
            (folder/"batch-report.json").write_text(json.dumps(batch))
            self.assertTrue(valid_cached(folder,REC))
            (folder/"example_0.table").write_bytes(b"tampered")
            self.assertFalse(valid_cached(folder,REC))
            (folder/"example_0.table").write_bytes(raw)
            batch["pins"]["mathlib_commit"]="b"*40
            (folder/"batch-report.json").write_text(json.dumps(batch))
            self.assertFalse(valid_cached(folder,REC))

if __name__=="__main__":
    unittest.main()
