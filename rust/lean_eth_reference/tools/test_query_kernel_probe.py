"""Fail-closed, offline validation of the original kernel-only root receipt."""
import json
import unittest

from query_kernel_probe import COMPILER, STATUS, validate_kernel_root
from query_stream_aot import DECLARATION


def root_receipt():
    return {
        "format": "original-query-kernel-root-v1",
        "status": STATUS,
        "root": DECLARATION,
        "compiler": COMPILER,
        "source_kind": "definition",
        "immediate_symbols": [COMPILER, DECLARATION.removesuffix(".program") + ".command"],
        "immediate_symbol_kinds": [
            {"name": COMPILER, "kind": "definition"},
            {"name": DECLARATION.removesuffix(".program") + ".command", "kind": "definition"},
        ],
        "expression_nodes": 8,
        "root_app_arity": 5,
        "transitive_computational_closure": False,
        "rust_executable": False,
        "independent_lean_rust_parity": False,
        "counting_parity": False,
        "resource_correspondence": False,
    }


class KernelRootReceiptTests(unittest.TestCase):
    def test_bounded_source_root_is_only_an_inventory(self):
        actual = validate_kernel_root(json.dumps(root_receipt()))
        self.assertEqual(actual["status"], STATUS)
        self.assertFalse(actual["rust_executable"])
        self.assertFalse(actual["transitive_computational_closure"])

    def test_no_promotion_by_claiming_unproved_gates(self):
        for key in ("transitive_computational_closure", "rust_executable",
                    "independent_lean_rust_parity", "counting_parity",
                    "resource_correspondence"):
            with self.subTest(key=key):
                fixture = root_receipt()
                fixture[key] = True
                with self.assertRaisesRegex(ValueError, "mismatch"):
                    validate_kernel_root(json.dumps(fixture))

    def test_source_identity_and_shape_are_strict(self):
        for key, value in (
            ("root", "OAI.Different.program"),
            ("compiler", "OAI.Other.compiled"),
            ("status", "SOURCE_GRAPH_COMPILED"),
            ("source_kind", "opaque"),
            ("root_app_arity", 3),
            ("expression_nodes", 513),
        ):
            with self.subTest(key=key):
                fixture = root_receipt()
                fixture[key] = value
                with self.assertRaises(ValueError):
                    validate_kernel_root(json.dumps(fixture))

    def test_classifications_follow_actual_symbol_identities(self):
        fixture = root_receipt()
        fixture["immediate_symbol_kinds"][1]["name"] = "OAI.Forged.command"
        with self.assertRaisesRegex(ValueError, "classifications"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["immediate_symbol_kinds"][0]["kind"] = "verified-computational"
        with self.assertRaisesRegex(ValueError, "classifications"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["immediate_symbol_kinds"].pop()
        with self.assertRaisesRegex(ValueError, "classifications"):
            validate_kernel_root(json.dumps(fixture))

    def test_refuse_missing_extra_duplicate_and_unbounded_symbols(self):
        fixture = root_receipt()
        del fixture["counting_parity"]
        with self.assertRaises(ValueError):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["unexpected"] = "source claim"
        with self.assertRaises(ValueError):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["immediate_symbols"] = [COMPILER, COMPILER]
        with self.assertRaises(ValueError):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["immediate_symbols"] = [f"OAI.x.{n}" for n in range(513)]
        with self.assertRaises(ValueError):
            validate_kernel_root(json.dumps(fixture))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            validate_kernel_root(json.dumps(root_receipt())[:-1] +
                                 ', "status": "SOURCE_GRAPH_COMPILED"}')


if __name__ == "__main__":
    unittest.main()
