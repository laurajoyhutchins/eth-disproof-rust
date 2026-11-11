"""Mutation tests for resource-profile validity and evidence boundaries."""
import importlib.util
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("observed_profile", HERE / "profile-full-machine-traces.py")
assert spec and spec.loader
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

def fixture() -> str:
    lines = []
    for size in range(5):
        for code in range(1 << size):
            for dirty in ("clean", "dirty"):
                case = f"{size}_{code}_{dirty}"
                lines += [f"machine|{case}|0|0|00||", f"machine|{case}|1|H|00||"]
    return "\n".join(lines) + "\n"

class ProfileTests(unittest.TestCase):
    def test_matching_trace_and_observed_stack_peaks(self):
        with TemporaryDirectory() as d:
            path = Path(d) / "full.trace"
            path.write_text(fixture())
            p = mod.profile(path)
            self.assertEqual(len(p), 62)
            self.assertEqual(p["4_15_clean"]["source_transitions"], 1)
            self.assertEqual(p["4_15_clean"]["peak_live_stack_bits"], 0)
    def test_stack_growth_by_two_is_rejected_even_when_halt_is_valid(self):
        with TemporaryDirectory() as d:
            path = Path(d) / "full.trace"
            path.write_text(fixture().replace("machine|0_0_clean|1|H|00||", "machine|0_0_clean|1|H|00|11|"))
            with self.assertRaises(ValueError):
                mod.profile(path)
    def test_two_stacks_cannot_change_in_one_source_transition(self):
        with TemporaryDirectory() as d:
            path = Path(d) / "full.trace"
            path.write_text(fixture().replace("machine|0_0_clean|1|H|00||", "machine|0_0_clean|1|H|00|1|0"))
            with self.assertRaises(ValueError):
                mod.profile(path)
    def test_missing_case_is_rejected(self):
        with TemporaryDirectory() as d:
            path = Path(d) / "full.trace"
            path.write_text(fixture().split("machine|0_0_clean|0|")[0])
            with self.assertRaises(ValueError):
                mod.profile(path)
if __name__ == "__main__":
    unittest.main()
