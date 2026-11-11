"""Static source navigation tests; no Lean runtime is required."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import source_inventory as inv


class InventoryTests(unittest.TestCase):
    def test_pinned_source_index(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder) / "upstream/openai-math/lean/OAI/Algorithms/SubexponentialSAT"
            base.mkdir(parents=True)
            (base / "BitProgram.lean").write_text(
                "import OAI.Algorithms.SubexponentialSAT.LeanCompat\n"
                "namespace Example\n"
                "private def step : Nat := 2\n"
                "theorem witness : True := by trivial\n")
            returns = [subprocess.CompletedProcess([], 0, inv.PIN + "\n", ""),
                       subprocess.CompletedProcess([], 0, "", "")]
            with mock.patch.object(inv.subprocess, "run", side_effect=returns):
                result = inv.collect(base)
            self.assertEqual(result["totals"]["modules"], 1)
            self.assertEqual(result["totals"]["lexical_declarations"], 3)
            self.assertEqual(result["files"][0]["declarations_lexical"][1]["name_token"], "step")
            self.assertEqual(result["files"][0]["imports"], ["OAI.Algorithms.SubexponentialSAT.LeanCompat"])

    def test_wrong_revision_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder) / "upstream/openai-math/lean/OAI/Algorithms/SubexponentialSAT"
            base.mkdir(parents=True)
            with mock.patch.object(inv.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "wrong\n", "")):
                with self.assertRaises(RuntimeError):
                    inv.collect(base)


if __name__ == "__main__":
    unittest.main()
