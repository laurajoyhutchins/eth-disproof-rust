"""Fail when root Cargo, CLI, CI or docs drift back to obsolete paths."""

from __future__ import annotations

from pathlib import Path
import tomllib
import unittest

ROOT = Path(__file__).resolve().parent.parent


class RepositoryLayoutTests(unittest.TestCase):
    def test_roots_and_workspace_boundaries(self):
        for path in (
            "compiler/Cargo.toml",
            "compiler/NativeRust.lean",
            "compiler/frontend/ffi/abi.c",
            "compiler/backend/src/reader/mod.rs",
            "compiler/runtime/rust/immutable_value.rs",
            "compiler/runtime/lean-c/src/lib.rs",
            "compiler/runtime/lean-c/abi.c",
            "compiler/runtime/lean-c/reference.c",
            "compiler/runtime/lean-c/check.sh",
            "eth/Cargo.toml",
            "compiler/cli/Cargo.toml",
            "compiler/cli/src/contract.rs",
            "compiler/cli/src/interface.rs",
            "compiler/cli/src/main.rs",
            "eth/src/bin/eth-compiler.rs",
            "experiments/lean-compiler-bootstrap/README.md",
        ):
            self.assertTrue((ROOT / path).is_file(), path)
        self.assertEqual(
            tomllib.loads((ROOT / "Cargo.toml").read_text())["workspace"]["members"],
            ["eth"],
        )
        self.assertIn(
            "[workspace]", (ROOT / "compiler/Cargo.toml").read_text()
        )
        for old in ("rust/native_lean_backend", "rust/lean_eth_reference", "tools/lean-rust-bootstrap"):
            self.assertFalse((ROOT / old).exists(), old)

    def test_compiler_cli_uses_canonical_backend(self):
        manifest = tomllib.loads((ROOT / "compiler/cli/Cargo.toml").read_text())
        self.assertEqual(manifest["package"]["name"], "lean-compiler-cli")
        self.assertEqual(manifest["bin"][0]["name"], "lean-rust-compiler")
        source = (ROOT / "compiler/cli/src/interface.rs").read_text()
        self.assertIn('scripts/compile-project.sh', source)
        self.assertIn('env!("CARGO_MANIFEST_DIR")', source)
        self.assertNotIn("lean_eth_reference", source)
        legacy = (ROOT / "eth/src/bin/eth-compiler.rs").read_text()
        self.assertIn("lean_compiler_cli::run()", legacy)
        self.assertNotIn("fn execute(", legacy)
        self.assertIn('lean-compiler-cli = { path = "../compiler/cli" }',
                      (ROOT / "eth/Cargo.toml").read_text())

    def test_active_workflows_use_current_paths(self):
        old = ("rust/native_lean_backend", "rust/lean_eth_reference", "tools/lean-rust-bootstrap")
        for workflow in sorted((ROOT / ".github/workflows").glob("*.yml")):
            content = workflow.read_text()
            for prefix in old:
                # Excession deliberately analyzes the pre-rename base tree.
                if workflow.name == "excession-native-refactor.yml" and prefix == old[0]:
                    self.assertIn("BASE_PREFIX=rust/native_lean_backend", content)
                    continue
                self.assertNotIn(prefix, content, f"{workflow}: {prefix}")


if __name__ == "__main__":
    unittest.main()
