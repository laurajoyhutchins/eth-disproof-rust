"""Offline checks for durable GitHub Actions source-program checkpoint wiring."""
from pathlib import Path
import re
import unittest


WORKFLOW = Path(__file__).resolve().parents[3] / ".github/workflows/original-compiled-batch.yml"


def step(text: str, label: str) -> str:
    return text.split("      - name: " + label + "\n", 1)[1].split(
        "      - name: ", 1
    )[0]


class GitHubCheckpointTests(unittest.TestCase):
    def test_restore_and_save_share_pinned_run_specific_cache_identity(self):
        workflow = WORKFLOW.read_text()
        restore = step(workflow, "Restore source-program checkpoints from previous GitHub runs")
        save = step(workflow, "Save source-program checkpoints for subsequent GitHub runs")
        restore_key = re.search(r"(?m)^\s+key: (original-lean-programs-v1-.*)$", restore)
        save_key = re.search(r"(?m)^\s+key: (original-lean-programs-v1-.*)$", save)
        self.assertIsNotNone(restore_key)
        self.assertIsNotNone(save_key)
        self.assertEqual(restore_key.group(1), save_key.group(1))
        key = restore_key.group(1)
        for component in (
            "runner.os", "github.run_id", "github.run_attempt",
            "4eaee87548250b2682affda7d05d947c05554bae",
            "export_compiled_batch.py", "extract_compiled_catalog.py",
            "export_source_program.lean", "lean-toolchain",
            "lake-manifest.json",
        ):
            with self.subTest(component=component):
                self.assertIn(component, key)
        self.assertIn("restore-keys: |", restore)
        self.assertIn(key.split("${{ github.run_id }}", 1)[0], restore)
        self.assertIn("path: ${{ runner.temp }}/original-compiled", restore)
        self.assertIn("path: ${{ runner.temp }}/original-compiled", save)
        self.assertIn("if: always()", save)
        self.assertIn("continue-on-error: true", save)
        self.assertIn("actions/cache/restore@", restore)
        self.assertIn("actions/cache/save@", save)

    def test_resume_is_remote_only_on_manual_compilation(self):
        workflow = WORKFLOW.read_text()
        # PRs should not perform Lean/Mathlib setup or touch GitHub cache.
        source_tools = workflow.split("  source-tools:", 1)[1].split(
            "  original-compiled-batch:", 1
        )[0]
        compile_job = workflow.split("  original-compiled-batch:", 1)[1]
        self.assertIn("if: github.event_name == 'pull_request'", source_tools)
        self.assertNotIn("actions/cache/", source_tools)
        self.assertIn("if: github.event_name == 'workflow_dispatch'", compile_job)
        self.assertIn("Restore source-program checkpoints", compile_job)
        self.assertIn("Save source-program checkpoints", compile_job)
        self.assertLess(
            compile_job.index("Restore source-program checkpoints"),
            compile_job.index("Compile a bounded batch"),
        )
        self.assertLess(
            compile_job.index("Compile a bounded batch"),
            compile_job.index("Save source-program checkpoints"),
        )
        self.assertLess(
            compile_job.index("Save source-program checkpoints"),
            compile_job.index("Generate and typecheck"),
        )


if __name__ == "__main__":
    unittest.main()
