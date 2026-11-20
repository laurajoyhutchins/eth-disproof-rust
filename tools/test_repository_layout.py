"""Fail when root Cargo, CLI, CI or docs drift back to obsolete paths."""

from __future__ import annotations

from pathlib import Path
from fnmatch import fnmatchcase
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
            "compiler/runtime/lean-c/generated_value.rs",
            "compiler/runtime/lean-c/heap_oracle.c",
            "compiler/runtime/lean-c/check-generated-heap.sh",
            "compiler/examples/RuntimeHeapKernels.lean",
            "compiler/examples/RuntimeHeapFixture.lean",
            "eth/Cargo.toml",
            "eth/src/error.rs",
            "verification/ranked-source/Cargo.toml",
            "verification/ranked-source/src/lib.rs",
            "verification/ranked-source/hax.toml",
            "compiler/cli/Cargo.toml",
            "compiler/cli/src/contract.rs",
            "compiler/cli/src/interface.rs",
            "compiler/cli/src/main.rs",
            "eth/src/bin/eth-compiler.rs",
            "eth/src/machine/native_frontend.rs",
            "eth/src/query/native_query_prefix.rs",
            "eth/src/counting/native_terminal_count.rs",
            "experiments/lean-compiler-bootstrap/README.md",
        ):
            self.assertTrue((ROOT / path).is_file(), path)
        self.assertEqual(
            tomllib.loads((ROOT / "Cargo.toml").read_text())["workspace"]["members"],
            ["eth", "verification/ranked-source"],
        )
        self.assertIn(
            "[workspace]", (ROOT / "compiler/Cargo.toml").read_text()
        )
        harness = (ROOT / "verification/ranked-source/src/lib.rs").read_text()
        for source in (
            "error.rs",
            "representation_ranked_certificate.rs",
            "representation_ranked_input.rs",
        ):
            self.assertIn(f'#[path = "../../../eth/src/{source}"]', harness)
            self.assertTrue((ROOT / "eth/src" / source).is_file())

        for old in ("rust/native_lean_backend", "rust/lean_eth_reference", "tools/lean-rust-bootstrap"):
            self.assertFalse((ROOT / old).exists(), old)

    def test_eth_modules_preserve_public_paths(self):
        source = (ROOT / "eth/src/lib.rs").read_text()
        for group, module in (
            ("machine", "native_frontend"),
            ("query", "native_query_prefix"),
            ("counting", "native_terminal_count"),
        ):
            self.assertIn(f'#[path = "{group}/{module}.rs"]', source)
            self.assertIn(f"pub mod {module};", source)
            self.assertFalse((ROOT / "eth/src" / f"{module}.rs").exists())

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


    def test_source_refinement_covers_physical_program_producers(self):
        # The deep Lean certificate gate must run when the shared Rust
        # instruction encoder changes, even if no proof file changes.
        workflow = (ROOT / ".github/workflows/lean-source-refinement.yml").read_text()
        self.assertEqual(workflow.count("  pull_request:\n    paths:\n"), 1)
        body = workflow.split("  pull_request:\n    paths:\n", 1)[1]
        patterns = []
        for line in body.splitlines():
            if line.startswith("      - '") and line.endswith("'"):
                patterns.append(line.removeprefix("      - '")[:-1])
            elif not line.strip() or line.lstrip().startswith("#"):
                continue
            else:
                break
        self.assertTrue(patterns, "source-refinement PR path filter is empty")
        for producer in (
            "eth/src/bit_program.rs",
            "eth/src/bit_program/physical_encoding.rs",
            "eth/src/bit_program/structured.rs",
            "eth/src/bit_program/frame_programs.rs",
            "eth/src/bit_program/record_iteration.rs",
            "eth/src/bit_program/source_json/codegen.rs",
            "eth/src/bin/framed-reader-certificate.rs",
            "eth/tools/verify_rust_physical_receipt.py",
            "eth/proofs/SourceGraphRefinement.lean",
            "instrumentation/lean-env/lean-toolchain",
            "instrumentation/lean-env/lakefile.lean",
            "instrumentation/lean-env/lake-manifest.json",
        ):
            self.assertTrue(
                any(fnmatchcase(producer, pattern) for pattern in patterns),
                f"source-refinement workflow misses {producer}",
            )


    def test_affine_verification_follows_its_inputs_and_dependency_lock(self):
        """One existing check follows its inputs, including source pins."""
        path = ROOT / ".github/workflows/egg-contraction-experiment.yml"
        workflow = path.read_text()
        manifest = ROOT / "experiments/egg-contraction-optimizer/Cargo.toml"
        lock = manifest.with_name("Cargo.lock")

        def event_paths(source: str, event: str) -> list[str]:
            # This workflow uses a literal paths list. Parse only that event
            # block, never unrelated job steps or a different event's paths.
            lines = source.splitlines()
            marker = f"  {event}:"
            self.assertIn(marker, lines)
            start = lines.index(marker) + 1
            block: list[str] = []
            for line in lines[start:]:
                if (line.startswith("  ") and not line.startswith("    ")
                        and not line.lstrip().startswith("#")) or line.startswith("jobs:"):
                    break
                block.append(line)
            self.assertIn("    paths:", block, f"missing {event} path filter")
            paths: list[str] = []
            for line in block[block.index("    paths:") + 1:]:
                stripped = line.strip()
                if stripped.startswith('- "') and stripped.endswith('"'):
                    paths.append(stripped[3:-1])
                elif stripped.startswith("- '") and stripped.endswith("'"):
                    paths.append(stripped[3:-1])
            self.assertTrue(paths, f"empty {event} path filter")
            return paths

        inputs = (
            "experiments/egg-contraction-optimizer/Cargo.toml",
            "experiments/egg-contraction-optimizer/Cargo.lock",
            "experiments/egg-contraction-optimizer/src/affine_native_lean.rs",
            "eth/proofs/IndependentAffineBoundary.lean",
            "eth/proofs/IndependentAffineRankNullity.lean",
            "eth/proofs/IndependentAffineRowOps.lean",
            "eth/proofs/IndependentAffinePackedRows.lean",
            "eth/proofs/IndependentAffineTerminal.lean",
            "eth/proofs/IndependentAffineSourceRows.lean",
            "eth/proofs/IndependentAffineNativeAudit.lean",
            "eth/proofs/IndependentAffineIndexToggle.lean",
            "eth/proofs/IndependentAffineMatrixReplay.lean",
            "instrumentation/lean-env/lean-toolchain",
            "instrumentation/lean-env/lakefile.lean",
            "instrumentation/lean-env/lake-manifest.json",
        )
        for event in ("pull_request", "push"):
            paths = event_paths(workflow, event)
            for dependency in inputs:
                self.assertTrue(
                    any(fnmatchcase(dependency, pattern) for pattern in paths),
                    f"{event} does not verify {dependency}",
                )
            # A non-affected documentation file must not start a deep proof.
            self.assertFalse(
                any(fnmatchcase("docs/STYLE.md", pattern) for pattern in paths),
                f"{event} path filter is broader than the proof inputs",
            )

        # Negative control: deleting both environment-manifest triggers
        # makes the very same matching rule fail.
        mutated = workflow.replace(
            '      - "instrumentation/lean-env/lake-manifest.json"\n', ""
        )
        for event in ("pull_request", "push"):
            self.assertFalse(any(
                fnmatchcase("instrumentation/lean-env/lake-manifest.json", pattern)
                for pattern in event_paths(mutated, event)
            ))

        self.assertIn(
            "cargo test --locked --manifest-path experiments/egg-contraction-optimizer/Cargo.toml",
            workflow,
        )
        self.assertNotIn("Capture resolved experiment dependency lock", workflow)
        self.assertIn("[workspace]", manifest.read_text())
        self.assertTrue(lock.is_file(), "standalone Cargo.lock must be committed")
        entries = tomllib.loads(lock.read_text())
        self.assertEqual(entries["version"], 4)
        packages = {package["name"]: package for package in entries["package"]}
        self.assertEqual(packages["egg"]["version"], "0.9.5")
        self.assertEqual(packages["num-bigint"]["version"], "0.4.6")
        self.assertIn("egg-contraction-experiment", packages)
        for package in entries["package"]:
            if package.get("source", "").startswith("registry+"):
                self.assertEqual(len(package.get("checksum", "")), 64, package["name"])



if __name__ == "__main__":
    unittest.main()
