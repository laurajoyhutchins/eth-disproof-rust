"""Keep source-executed Lean stage mappings aligned with checked-in probes."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import capture


class ProbeRegistryTests(unittest.TestCase):
    def test_every_declared_probe_is_present(self):
        root = Path(__file__).resolve().parents[1] / "probes"
        for stage, definition in capture.STAGES.items():
            with self.subTest(stage=stage):
                file = root / definition.file
                self.assertTrue(file.is_file(), f"{stage} points at missing {definition.file}")
                self.assertTrue(file.read_text().startswith("import "), "must import pinned Lean source")

    def test_targeted_odometer_does_not_import_unrelated_high_programs(self):
        probe = (Path(__file__).resolve().parents[1] / "probes" /
                 capture.STAGES["machine-odometer"].file).read_text()
        self.assertIn("import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer", probe)
        self.assertNotIn("import OAI.Algorithms.SubexponentialSAT.SqrtLog.", probe)
        self.assertNotIn("import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.", probe)


if __name__ == "__main__":
    unittest.main()
