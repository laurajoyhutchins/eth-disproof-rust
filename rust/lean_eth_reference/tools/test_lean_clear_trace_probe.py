"""Strict, adversarial shape tests for actual Lean clearProgram step receipts."""
import json
import unittest

from lean_clear_trace_probe import (
    DECLARATION, PREFIX, SOURCE_COMMIT, WORDS, validate,
)


def fixture():
    cases = []
    for word in WORDS:
        remaining = list(word)
        states = [{
            "pc": 0,
            "regs": [False, False, True],
            "stacks": [[], list(remaining), [], [False, True]],
        }]
        while remaining:
            top = remaining.pop(0)
            states.append({
                "pc": 1,
                "regs": [top, True, True],
                "stacks": [[], list(remaining), [], [False, True]],
            })
            states.append({
                "pc": 0,
                "regs": [top, True, True],
                "stacks": [[], list(remaining), [], [False, True]],
            })
        states.append({
            "pc": 1,
            "regs": [False, False, True],
            "stacks": [[], [], [], [False, True]],
        })
        states.append({
            "pc": 2,
            "regs": [False, False, True],
            "stacks": [[], [], [], [False, True]],
        })
        states.append({
            "pc": None,
            "regs": [False, False, True],
            "stacks": [[], [], [], [False, True]],
        })
        cases.append({"word": word, "states": states,
                      "source_steps": 2*len(word)+3})
    return {
        "format": "original-lean-clearprogram-steps-v1",
        "source_commit": SOURCE_COMMIT,
        "declaration": DECLARATION,
        "r": 3, "s": 4, "labels": 3,
        "source_stack": 1, "value_register": 0, "present_register": 1,
        "cases": cases,
        "independent_lean_rust_parity_proved": False,
    }


def encode(obj):
    return PREFIX + json.dumps(obj)


class LeanTraceShapeTests(unittest.TestCase):
    def test_reference_shaped_cases(self):
        value = fixture()
        self.assertEqual(validate(encode(value)), value)

    def test_duplicate_or_missing_source_reports_refuse(self):
        x = encode(fixture())
        for wrong in ("", x + "\n" + x, x.replace(PREFIX, "OTHER=")):
            with self.subTest(value=wrong[:25]), self.assertRaises(ValueError):
                validate(wrong)

    def test_bad_counts_shapes_and_certification_refuse(self):
        for kind in ("source", "table", "certificate", "missing",
                     "step", "pc", "word", "reg", "frame", "halt"):
            with self.subTest(kind=kind):
                r = fixture()
                if kind == "source":
                    r["source_commit"] = "f" * 40
                elif kind == "table":
                    r["labels"] = 4
                elif kind == "certificate":
                    r["independent_lean_rust_parity_proved"] = True
                elif kind == "missing":
                    r["cases"].pop()
                elif kind == "step":
                    r["cases"][2]["states"].pop()
                elif kind == "pc":
                    r["cases"][1]["states"][1]["pc"] = 7
                elif kind == "word":
                    r["cases"][1]["word"] = [False]
                elif kind == "reg":
                    r["cases"][1]["states"][1]["regs"][0] = 1
                elif kind == "frame":
                    r["cases"][1]["states"][-1]["stacks"][3] = []
                else:
                    r["cases"][2]["states"][-1]["pc"] = 2
                with self.assertRaises(ValueError):
                    validate(encode(r))


if __name__ == "__main__":
    unittest.main()
