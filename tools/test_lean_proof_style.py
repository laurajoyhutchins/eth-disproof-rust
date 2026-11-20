"""Positive and negative controls for the Lean proof style boundary."""
from pathlib import Path
import tempfile
import unittest

from check_lean_proof_style import (
    check_text,
    discover_proof_modules,
    undocumented_declarations,
)


GOOD = """import Mathlib

/-!
# Example module
-/

namespace Example

/-- An elementary proposition. -/
theorem self_evident : True := by
  trivial

end Example
"""


class ProofStyleTests(unittest.TestCase):
    def test_discovers_both_authored_proof_roots_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            selected = (
                Path("eth/proofs/IndependentExample.lean"),
                Path("instrumentation/lean-env/ACC/ExampleProof.lean"),
            )
            for relative in selected:
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(GOOD, encoding="utf-8")
            upstream = root / "upstream/anthropic/Proof.lean"
            upstream.parent.mkdir(parents=True)
            upstream.write_text(GOOD, encoding="utf-8")
            self.assertEqual(
                [path.relative_to(root) for path in discover_proof_modules(root)],
                sorted(selected),
            )

    def test_annotated_undocumented_theorem_is_reported(self):
        source = GOOD.replace("/-- An elementary proposition. -/\\n", "")
        source = source.replace("theorem self_evident", "@[simp] theorem self_evident")
        self.assertEqual(len(undocumented_declarations(source)), 1)

    def test_valid_module(self):
        self.assertEqual(check_text(GOOD), [])

    def test_requires_declaration_doc(self):
        source = GOOD.replace("/-- An elementary proposition. -/\n", "")
        self.assertTrue(any("needs /--" in e for e in check_text(source, strict_docs=True)))

    def test_advisory_does_not_block_existing_helpers(self):
        source = GOOD.replace("/-- An elementary proposition. -/\n", "")
        self.assertEqual(check_text(source), [])
        self.assertEqual(len(undocumented_declarations(source)), 1)

    def test_module_comment_not_declaration_doc(self):
        source = GOOD.replace(
            "/-- An elementary proposition. -/\n",
            "/- Ordinary comment. -/\n",
        )
        self.assertTrue(any("needs /--" in e for e in check_text(source, strict_docs=True)))

    def test_requires_module_comment(self):
        source = GOOD.replace("/-!\n# Example module\n-/\n\n", "")
        self.assertTrue(any("module documentation" in e for e in check_text(source)))

    def test_rejects_whitespace_and_long_lines(self):
        source = GOOD.replace("  trivial", "  trivial " + "x" * 110 + "\t ")
        errors = check_text(source)
        self.assertTrue(any("tabs" in e for e in errors))
        self.assertTrue(any("trailing whitespace" in e for e in errors))
        self.assertTrue(any("100 characters" in e for e in errors))

    def test_requires_one_newline(self):
        self.assertTrue(any("EOF" in e for e in check_text(GOOD.rstrip("\n"))))
        self.assertTrue(any("EOF" in e for e in check_text(GOOD + "\n")))

    def test_rejects_three_blank_lines(self):
        self.assertTrue(any("blank line" in e for e in check_text(GOOD.replace(
            "namespace Example\n\n", "namespace Example\n\n\n\n"
        ))))


if __name__ == "__main__":
    unittest.main()
