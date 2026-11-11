"""Offline regression tests for the resumable Lean-to-Rust driver."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from lean_rust import identity, resolve, valid_cached
from export_compiled_batch import SOURCE_SHA

REC = {"id":"example_0","fqn":"OAI.Algorithms.SubexponentialSAT.Example.program",
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

    def test_cached_receipt_requires_matching_original_bytes(self):
        with tempfile.TemporaryDirectory() as temp:
            folder=Path(temp)
            self.assertFalse(valid_cached(folder,REC))
            raw=(f"PIN|example_0|{SOURCE_SHA}|{REC['git_blob']}\n"
                 "PROGRAM|example_0|1|1|1|0|0|0\n"
                 "CODE|example_0|0|halt\n"
                 "END|example_0|1\n").encode("ascii")
            (folder/"example_0.table").write_bytes(raw)
            receipt={"source_commit":SOURCE_SHA,"source_git_blob":REC["git_blob"],
                     "declaration":REC["fqn"],"status":"EXPORTED_FROM_PINNED_LEAN",
                     "sha256":hashlib.sha256(raw).hexdigest(),"bytes":len(raw)}
            (folder/"example_0.receipt.json").write_text(json.dumps(receipt))
            self.assertTrue(valid_cached(folder,REC))
            (folder/"example_0.table").write_bytes(b"tampered")
            self.assertFalse(valid_cached(folder,REC))

if __name__=="__main__":
    unittest.main()
