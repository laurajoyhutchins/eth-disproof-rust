"""Both routes share this fail-closed acceptance contract. No semantic proof claimed."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from lean_codegen_contract import (Refusal, main, source_identity, validate_contract,
                                   validate_residual)


def name(*parts: str):
    result = {"tag": "anonymous"}
    for p in parts:
        result = {"tag": "str", "parent": result, "value": p}
    return result


def residual(root="Demo.double") -> bytes:
    obj = {
        "format": "lean-core-expr-dag-v1", "status": "residualized-unverified",
        "source": name(*root.split('.')),
        "source_root": 0, "reduced_root": 0,
        "nodes": [{"tag": "const", "name": name("Nat", "zero"), "levels": []}],
        "node_count": 1, "source_symbols": ["Nat.zero"],
        "metadata_dropped": 0, "lean_defeq_checked": True,
        "beta_zeta_steps": 0, "rust_executable": False,
        "physical_refinement": "not-established",
    }
    return (json.dumps(obj, separators=(',', ':')) + '\n').encode()


def ir_report(code: bytes) -> bytes:
    return json.dumps({
        "format": "lean-compiler-ir-backend-probe-v1", "status": "generated-unverified",
        "module": "Demo", "roots": ["Demo.double"],
        "lean_toolchain": "leanprover/lean4:v4.35.0",
        "lean_version": "Lean (version 4.35.0, test)",
        "semantic_verification": "not-established",
        "physical_bitprogram_verification": "not-established",
        "generated_sha256": hashlib.sha256(code).hexdigest(),
        "generated_bytes": len(code),
        "backend_summary": {"module": "Demo", "functions": 1, "public": [
            {"lean": "Demo.double", "rust": "demo_double"}], "skipped": []},
    }).encode()


class ContractTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        for args in (("init", "-q"), ("config", "user.email", "test@example.org"),
                     ("config", "user.name", "Test")):
            subprocess.run(["git", "-C", str(self.repo), *args], check=True)
        (self.repo / "Demo.lean").write_text("namespace Demo\ndef double (n : Nat) := n+n\nend Demo\n")
        (self.repo / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        subprocess.run(["git", "-C", str(self.repo), "add", "Demo.lean", "lean-toolchain"], check=True)
        subprocess.run(["git", "-C", str(self.repo), "commit", "-qm", "pin source"], check=True)
        self.rev = subprocess.check_output(["git", "-C", str(self.repo), "rev-parse", "HEAD"], text=True).strip()
        self.source = source_identity(self.repo, "Demo.lean", self.rev)

    def checked(self, backend, artifact, report=None):
        return validate_contract(backend=backend, artifact=artifact, report=report,
                                 module="Demo", roots=["Demo.double"], source=self.source)

    def test_both_paths_remain_unverified(self):
        raw = residual()
        code = b"pub fn double(n: u64) -> u64 { n+n }\n"
        for backend, artifact, upstream in (
            ("residual-expr", raw, None), ("compiler-ir", code, ir_report(code))
        ):
            with self.subTest(backend=backend):
                receipt = self.checked(backend, artifact, upstream)
                self.assertEqual(receipt["artifact_sha256"], hashlib.sha256(artifact).hexdigest())
                self.assertEqual(receipt["source_file"], self.source)
                self.assertFalse(receipt["executable_approved"])
                self.assertEqual(receipt["checks"]["declaration_source_binding"], "not-established")
                self.assertEqual(receipt["checks"]["physical_bitprogram_refinement"], "not-established")

    def test_ir_hash_skips_and_identity_fail_closed(self):
        code = b"fn double() {}\n"
        receipt = json.loads(ir_report(code))
        for change in ("sha", "bytes", "skip", "roots", "status", "semantic", "toolchain"):
            with self.subTest(change=change):
                d = json.loads(json.dumps(receipt))
                if change == "sha": d["generated_sha256"] = "0" * 64
                if change == "bytes": d["generated_bytes"] += 1
                if change == "skip": d["backend_summary"]["skipped"].append({"name": "M.x", "reason": "missing IR"})
                if change == "roots": d["roots"] = ["Wrong.entry"]
                if change == "status": d["status"] = "verified-executable"
                if change == "semantic": d["semantic_verification"] = "verified"
                if change == "toolchain": d["lean_toolchain"] = "leanprover/lean4:v4.34.1"
                with self.assertRaises(Refusal):
                    self.checked("compiler-ir", code, json.dumps(d).encode())

    def test_symbolic_identity_executability_and_graph_refusal(self):
        d = json.loads(residual())
        for change in ("root", "execution", "physical", "count", "future", "cycle"):
            with self.subTest(change=change):
                value = json.loads(json.dumps(d))
                if change == "root": value["source"] = name("Wrong", "root")
                if change == "execution": value["rust_executable"] = True
                if change == "physical": value["physical_refinement"] = "proved"
                if change == "count": value["node_count"] = 2
                if change == "future": value["nodes"].append({"tag": "unknown", "foo": 0}); value["node_count"] = 2
                if change == "cycle": value["nodes"][0] = {"tag": "app", "fn": 0, "arg": 0}
                with self.assertRaises(Refusal):
                    self.checked("residual-expr", (json.dumps(value) + "\n").encode())

    def test_dup_json_refusal(self):
        raw = residual().replace(b'"rust_executable":false', b'"rust_executable":false,"rust_executable":true')
        with self.assertRaisesRegex(Refusal, "duplicate"):
            self.checked("residual-expr", raw)

    def test_modified_or_wrong_source_revision_refuses(self):
        (self.repo / "Demo.lean").write_text("namespace Demo\ndef double (n : Nat) := n*n\nend Demo\n")
        with self.assertRaisesRegex(Refusal, "does not match"):
            source_identity(self.repo, "Demo.lean", self.rev)
        with self.assertRaises(Refusal):
            source_identity(self.repo, "Demo.lean", "f" * 40)

    def test_mutated_source_toolchain_refuses(self):
        (self.repo / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
        with self.assertRaisesRegex(Refusal, "not pinned"):
            source_identity(self.repo, "Demo.lean", self.rev)

    def test_no_stale_contract_receipt_on_refusal(self):
        artifact = self.repo / "output.json"
        artifact.write_bytes(residual())
        target = self.repo / "contract.json"
        options = ["--backend", "residual-expr", "--artifact", str(artifact),
                   "--module", "Demo", "--root", "Demo.double",
                   "--source-repo", str(self.repo), "--source-path", "Demo.lean",
                   "--source-revision", self.rev, "--receipt", str(target)]
        self.assertEqual(main(options), 0)
        self.assertTrue(target.exists())
        artifact.write_bytes(residual("Other.root"))
        self.assertEqual(main(options), 2)
        self.assertFalse(target.exists())

    def test_real_lean_residual_graph_smoke_when_supplied(self):
        # Genuine Lean output is passed in CI via a fixture path, not mocked.
        import os
        file = os.environ.get("REAL_LEAN_RESIDUAL_JSON")
        if file:
            d = validate_residual(Path(file).read_bytes(), "Shared.root")
            self.assertGreater(d["node_count"], 5)


if __name__ == "__main__":
    unittest.main()
