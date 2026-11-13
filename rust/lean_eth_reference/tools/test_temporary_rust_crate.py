"""Regression tests for the temporary Rust build boundary of Lean acceptance."""
import tempfile
from pathlib import Path
import tomllib
import unittest

from temporary_rust_crate import isolated_cargo_manifest


class IsolatedCargoManifestTests(unittest.TestCase):
    def test_nested_generated_crate_is_an_independent_workspace(self):
        with tempfile.TemporaryDirectory() as root:
            dependency = Path(root) / "Rust source with spaces" / "lean_eth_reference"
            raw = isolated_cargo_manifest("lean-physical-differential", dependency)
            parsed = tomllib.loads(raw)
            self.assertEqual(parsed["package"]["name"], "lean-physical-differential")
            self.assertEqual(parsed["workspace"], {})
            self.assertEqual(parsed["dependencies"]["lean_eth_reference"]["package"], "lean-eth-reference")
            self.assertEqual(parsed["dependencies"]["lean_eth_reference"]["path"], str(dependency.resolve()))

    def test_refuses_cargo_manifest_injection(self):
        with self.assertRaises(ValueError):
            isolated_cargo_manifest('test"\n[dependencies]', Path("/tmp/project"))
        with self.assertRaises(ValueError):
            isolated_cargo_manifest("", Path("/tmp/project"))


if __name__ == "__main__":
    unittest.main()
