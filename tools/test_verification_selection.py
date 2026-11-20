"""Mutation tests for proof-workflow dependency selection."""
from __future__ import annotations

from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from verify_workflow_selection import (
    ROOT, covered, pull_request_paths, verify_all, verify_selection,
)


def put(root: Path, name: str, contents: str) -> None:
    file = root / name
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(contents, encoding="utf-8")


class VerificationSelectionTests(unittest.TestCase):
    def test_actual_workflows_cover_their_executed_dependencies(self):
        verify_all(ROOT)

    def test_github_globs_do_not_allow_a_single_star_to_cross_directory(self):
        self.assertFalse(covered("eth/proofs/nested/Example.lean", ("eth/proofs/*.lean",)))
        self.assertTrue(covered("eth/proofs/nested/Example.lean", ("eth/proofs/**",)))
        self.assertTrue(covered("eth/tools/export_compiled_batch.py", ("eth/tools/*compiled*.py",)))
        self.assertFalse(covered("eth/tools/deep/export_compiled_batch.py",
                                 ("eth/tools/*compiled*.py",)))

    def test_mutated_selection_and_unsupported_filter_refuse(self):
        source = (ROOT / ".github/workflows/lean-independent-formulations.yml").read_text()
        missing = source.replace(
            "      - 'instrumentation/lean-env/lakefile.lean'\n", "", 1)
        self.assertNotEqual(source, missing)
        with self.assertRaisesRegex(ValueError, "skips actual verification dependencies"):
            verify_selection(ROOT, "lean-independent-formulations.yml", missing)
        invalid = source.replace("      - 'instrumentation/lean-env/lakefile.lean'",
                                 "      - '!instrumentation/lean-env/lakefile.lean'", 1)
        with self.assertRaisesRegex(ValueError, "unsupported GitHub path selector"):
            pull_request_paths(invalid)

    def test_new_transitive_lean_import_must_have_a_selector(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            put(root, "eth/proofs/Example.lean", "import ACC.Foundation\n")
            put(root, "instrumentation/lean-env/ACC/Foundation.lean",
                "import ACC.NewLemma\n")
            put(root, "instrumentation/lean-env/ACC/NewLemma.lean", "theorem example : True := by trivial\n")
            for pin in ("lean-toolchain", "lakefile.lean", "lake-manifest.json"):
                put(root, "instrumentation/lean-env/" + pin, "pin\n")
            workflow = (
                "on:\n  pull_request:\n    paths:\n"
                "      - 'eth/proofs/Example.lean'\n"
                "      - 'instrumentation/lean-env/ACC/Foundation.lean'\n"
                "      - 'instrumentation/lean-env/lean-toolchain'\n"
                "      - 'instrumentation/lean-env/lakefile.lean'\n"
                "      - 'instrumentation/lean-env/lake-manifest.json'\n"
                "      - '.github/workflows/lean-source-refinement.yml'\n"
                "jobs:\n  lean:\n    steps:\n"
                "      - run: lake env lean \"$GITHUB_WORKSPACE/eth/proofs/Example.lean\"\n"
            )
            with self.assertRaisesRegex(ValueError, "NewLemma"):
                verify_selection(root, "lean-source-refinement.yml", workflow)
            trigger = "      - 'instrumentation/lean-env/ACC/NewLemma.lean'\n"
            fixed = workflow.replace("    paths:\n", "    paths:\n" + trigger)
            required = verify_selection(root, "lean-source-refinement.yml", fixed)
            self.assertIn("instrumentation/lean-env/ACC/NewLemma.lean", required)

    def test_new_python_import_must_have_a_selector(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            put(root, "eth/tools/driver.py", "from helper import main\n")
            put(root, "eth/tools/helper.py", "from nested import work\n")
            put(root, "eth/tools/nested.py", "def work(): pass\n")
            for pin in ("lean-toolchain", "lakefile.lean", "lake-manifest.json"):
                put(root, "instrumentation/lean-env/" + pin, "pin\n")
            workflow = (
                "on:\n  pull_request:\n    paths:\n"
                "      - 'eth/tools/driver.py'\n"
                "      - 'eth/tools/helper.py'\n"
                "      - 'instrumentation/lean-env/lean-toolchain'\n"
                "      - 'instrumentation/lean-env/lakefile.lean'\n"
                "      - 'instrumentation/lean-env/lake-manifest.json'\n"
                "      - '.github/workflows/original-source-graph.yml'\n"
                "jobs:\n  check:\n    steps:\n"
                "      - run: python3 eth/tools/driver.py\n"
            )
            with self.assertRaisesRegex(ValueError, "nested.py"):
                verify_selection(root, "original-source-graph.yml", workflow)
            fixed = workflow.replace("    paths:\n",
                                     "    paths:\n      - 'eth/tools/nested.py'\n")
            self.assertIn("eth/tools/nested.py",
                          verify_selection(root, "original-source-graph.yml", fixed))


if __name__ == "__main__":
    unittest.main()
