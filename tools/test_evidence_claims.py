"""Adversarial tests for the scoped evidence ledger and exact-head receipts."""

from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from check_evidence_claims import LEDGER, ROOT, ReceiptError, audit, git_blob_sha


class EvidenceReceiptTests(unittest.TestCase):
    def setUp(self):
        self.directory = TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        path = self.root / "src/model.lean"
        path.parent.mkdir(parents=True)
        path.write_bytes(b"namespace Model\ntheorem example : True := by trivial\nend Model\n#print axioms Model.example\n")
        self.subject = path
        self.example = {
            "schema": "eth-scoped-receipts/v1",
            "claims": [{
                "id": "a-model-claim",
                "statement": "The tiny abstract model has a checked theorem.",
                "kind": "abstract_lean_model",
                "quantifier": "all_admitted_model_states",
                "domain": "Lean models with this precise assumption.",
                "observation": "Abstract theorem proposition only.",
                "excluded": ["No compiled Rust execution or physical runtime semantics."],
                "theorem": "Model.example",
                "receipt": {
                    "repository": "laurajoyhutchins/eth-disproof-rust",
                    "checked_head": "1" * 40,
                    "workflow": ".github/workflows/native-lean-rust.yml",
                    "run_id": 123,
                    "job": "native-ffi-smoke",
                    "step": "Kernel-check model",
                },
                "files": [{
                    "path": "src/model.lean",
                    "blob_sha": git_blob_sha(path.read_bytes()),
                }],
            }],
        }

    def remote(self, url):
        if "/git/trees/" in url:
            return {"truncated": False, "tree": [{
                "type": "blob",
                "path": "src/model.lean",
                "sha": git_blob_sha(self.subject.read_bytes()),
            }]}
        if url.endswith("/jobs?per_page=100"):
            return {"total_count": 1, "jobs": [{
                "name": "native-ffi-smoke",
                "conclusion": "success",
                "steps": [{"name": "Kernel-check model", "conclusion": "success"}],
            }]}
        return {
            "repository": {"full_name": "laurajoyhutchins/eth-disproof-rust"},
            "head_sha": "1" * 40,
            "path": ".github/workflows/native-lean-rust.yml",
            "status": "completed",
            "conclusion": "success",
        }

    def test_pinned_source_and_exact_remote_step(self):
        local = audit(self.example, self.root)
        self.assertEqual(local[0]["remote_receipt"], "not_checked")
        self.assertEqual(local[0]["semantic_promotion"], "none")
        remote = audit(self.example, self.root, fetcher=self.remote)
        self.assertEqual(remote[0]["remote_receipt"], "workflow_job_step_passed")
        self.assertEqual(remote[0]["source_pins"], "match_current_bytes")

    def test_stale_source_bytes_refuse(self):
        self.subject.write_bytes(b"theorem model : False := by sorry\n")
        with self.assertRaisesRegex(ReceiptError, "stale source blob"):
            audit(self.example, self.root)

    def test_wrong_workflow_head_refuses(self):
        payload = deepcopy(self.example)
        payload["claims"][0]["receipt"]["checked_head"] = "2" * 40
        with self.assertRaisesRegex(ReceiptError, "wrong repository/head/workflow"):
            audit(payload, self.root, fetcher=self.remote)

    def test_run_head_does_not_own_claimed_blob_refuses(self):
        def wrong_tree(url):
            result = self.remote(url)
            if "/git/trees/" in url:
                result["tree"][0]["sha"] = "f" * 40
            return result
        with self.assertRaisesRegex(ReceiptError, "claimed blob not present"):
            audit(self.example, self.root, fetcher=wrong_tree)

    def test_truncated_historical_tree_refuses(self):
        def truncated(url):
            result = self.remote(url)
            if "/git/trees/" in url:
                result["truncated"] = True
            return result
        with self.assertRaisesRegex(ReceiptError, "incomplete historical source tree"):
            audit(self.example, self.root, fetcher=truncated)

    def test_workflow_success_without_required_step_refuses(self):
        def wrong_step(url):
            result = self.remote(url)
            if "jobs?" in url:
                result["jobs"][0]["steps"] = [{"name": "Other step", "conclusion": "success"}]
            return result
        with self.assertRaisesRegex(ReceiptError, "required proof/test step"):
            audit(self.example, self.root, fetcher=wrong_step)

    def test_run_success_without_job_refuses(self):
        def no_job(url):
            result = self.remote(url)
            if "jobs?" in url:
                result["jobs"] = []
                result["total_count"] = 0
            return result
        with self.assertRaisesRegex(ReceiptError, "required job"):
            audit(self.example, self.root, fetcher=no_job)

    def test_incomplete_paginated_jobs_refuse(self):
        def missing_page(url):
            result = self.remote(url)
            if "jobs?" in url:
                result["total_count"] = 2
            return result
        with self.assertRaisesRegex(ReceiptError, "paginated job results"):
            audit(self.example, self.root, fetcher=missing_page)

    def test_unsupported_proof_tier_and_quantifier_refuse(self):
        for kind, quantifier in (
            ("actual_rust_refines_lean", "all_inputs"),
            ("bounded_compiler_guard", "all_inputs"),
            ("abstract_lean_model", "finite_fixtures"),
        ):
            with self.subTest(kind=kind, quantifier=quantifier):
                payload = deepcopy(self.example)
                payload["claims"][0]["kind"] = kind
                payload["claims"][0]["quantifier"] = quantifier
                with self.assertRaisesRegex(ReceiptError, "unsupported proof tier"):
                    audit(payload, self.root)

    def test_missing_exclusions_and_duplicate_claims_refuse(self):
        payload = deepcopy(self.example)
        payload["claims"][0]["excluded"] = []
        with self.assertRaisesRegex(ReceiptError, "excluded interpretations"):
            audit(payload, self.root)
        payload = deepcopy(self.example)
        payload["claims"].append(deepcopy(payload["claims"][0]))
        with self.assertRaisesRegex(ReceiptError, "repeated claim"):
            audit(payload, self.root)

    def test_unsafe_path_and_unexpected_field_refuse(self):
        payload = deepcopy(self.example)
        payload["claims"][0]["files"][0]["path"] = "../src/model.lean"
        with self.assertRaisesRegex(ReceiptError, "unsafe source path"):
            audit(payload, self.root)
        payload = deepcopy(self.example)
        payload["claims"][0]["verified"] = True
        with self.assertRaisesRegex(ReceiptError, "expected exactly"):
            audit(payload, self.root)

    def test_empty_ledger_is_safe_and_does_not_require_a_fake_receipt(self):
        self.assertEqual(
            audit({"schema": "eth-scoped-receipts/v1", "claims": []}, self.root),
            [],
        )

    def test_unsubstantiated_model_theorem_refuses(self):
        payload = deepcopy(self.example)
        payload["claims"][0]["theorem"] = "Model.notActuallyHere"
        with self.assertRaisesRegex(ReceiptError, "theorem/axiom audit"):
            audit(payload, self.root)

    def test_real_repository_claims_have_current_byte_pins(self):
        self.assertEqual(LEDGER.parent.parent.parent.resolve(), ROOT.resolve())
        claims = audit(json.loads(LEDGER.read_text()), ROOT)
        self.assertGreaterEqual(len(claims), 2)
        self.assertEqual({c["source_pins"] for c in claims}, {"match_current_bytes"})
        self.assertEqual({c["semantic_promotion"] for c in claims}, {"none"})


if __name__ == "__main__":
    unittest.main()
