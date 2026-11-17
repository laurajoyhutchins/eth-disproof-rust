"""Tests of the virtual source tree and source-link rewriting."""

from __future__ import annotations

import unittest

from tools.mkdocs_hooks import rewrite_source_links, source_paths


class MkdocsHookTests(unittest.TestCase):
    def test_source_tree_is_complete_and_unique(self):
        paths = source_paths()
        self.assertIn("README.md", paths)
        self.assertIn("CONTRIBUTING.md", paths)
        self.assertIn("research/two-adic-recursion.md", paths)
        self.assertIn("eth/docs/evidence.md", paths)
        self.assertIn("compiler/SEMANTICS.md", paths)
        self.assertIn("compiler/docs/backend-first-architecture.md", paths)
        self.assertIn("compiler/docs/compiler-status.md", paths)
        self.assertIn("compiler/docs/execution-runtime-contract.md", paths)
        self.assertGreaterEqual(len(paths), 50)
        self.assertEqual(len(paths), len(set(paths)))

    def test_document_link_stays_local(self):
        link = "[research](research/README.md)"
        self.assertEqual(link, rewrite_source_links(link, "README.md"))

    def test_source_file_points_to_github(self):
        result = rewrite_source_links(
            "[source](../reference/source-manifest.json)",
            "eth/docs/evidence.md",
        )
        self.assertEqual(
            "[source](https://github.com/laurajoyhutchins/eth-disproof-rust/"
            "blob/main/eth/reference/source-manifest.json)",
            result,
        )

    def test_source_directory_and_fragments(self):
        base = "eth/docs/evidence.md"
        self.assertIn("/tree/main/eth/src)",
                      rewrite_source_links("[source](../src)", base))
        self.assertIn("native_terminal.rs#L4)",
                      rewrite_source_links("[source](../src/native_terminal.rs#L4)", base))

    def test_remote_anchors_and_missing_are_not_masked(self):
        raw = "[site](https://example.com/foo) [jump](#section) [missing](no-such-page.md)"
        self.assertEqual(raw, rewrite_source_links(raw, "README.md"))

    def test_code_fences_are_preserved(self):
        tick = chr(96) * 3
        raw = (
            tick + "md\n"
            + "[source](eth/reference/source-manifest.json)\n"
            + tick + "\n"
            + "[source](eth/reference/source-manifest.json)\n"
        )
        result = rewrite_source_links(raw, "README.md")
        self.assertIn(tick + "md\n[source](eth/reference/source-manifest.json)", result)
        self.assertIn("/blob/main/eth/reference/source-manifest.json", result)


if __name__ == "__main__":
    unittest.main()
