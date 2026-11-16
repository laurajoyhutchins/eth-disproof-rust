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
        "command_name": DECLARATION.removesuffix(".program") + ".command",
        "command_expression_nodes": 24,
        "command_immediate_symbols": [
            "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq",
            "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.prepareHigh",
            DECLARATION.removesuffix(".program") + ".nodes",
            "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command",
        ],
        "command_symbol_kinds": [
            {"name": "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq",
             "kind": "constructor"},
            {"name": "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.prepareHigh",
             "kind": "definition"},
            {"name": DECLARATION.removesuffix(".program") + ".nodes",
             "kind": "definition"},
            {"name": "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command",
             "kind": "definition"},
        ],
        "same_module_local_declarations": [
            {
                "name": DECLARATION, "kind": "definition", "body_scanned": True,
                "expression_nodes": 8,
                "immediate_symbols": [
                    COMPILER, DECLARATION.removesuffix(".program") + ".command",
                ],
            },
            {
                "name": DECLARATION.removesuffix(".program") + ".command",
                "kind": "definition", "body_scanned": True,
                "expression_nodes": 24,
                "immediate_symbols": [
                    "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq",
                    "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.prepareHigh",
                    DECLARATION.removesuffix(".program") + ".nodes",
                    "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command",
                ],
            },
            {
                "name": DECLARATION.removesuffix(".program") + ".nodes",
                "kind": "definition", "body_scanned": True,
                "expression_nodes": 3,
                "immediate_symbols": ["OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq"],
            },
        ],
        "external_module_edges_unresolved": True,
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

    def test_original_command_shape_cannot_be_silently_substituted(self):
        fixture = root_receipt()
        fixture["command_immediate_symbols"].remove(
            "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command")
        with self.assertRaisesRegex(ValueError, "source shape"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["command_symbol_kinds"][0]["name"] = "OAI.Forged.Cmd.seq"
        with self.assertRaisesRegex(ValueError, "classifications"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["command_expression_nodes"] = 2048
        with self.assertRaisesRegex(ValueError, "node budget"):
            validate_kernel_root(json.dumps(fixture))

    def test_same_module_inventory_is_bounded_and_closed_without_executable_promotion(self):
        actual = validate_kernel_root(json.dumps(root_receipt()))
        self.assertEqual(len(actual["same_module_local_declarations"]), 3)
        self.assertTrue(actual["external_module_edges_unresolved"])
        self.assertFalse(actual["transitive_computational_closure"])

    def test_same_module_refuses_missing_dangling_duplicate_and_unreachable_nodes(self):
        fixture = root_receipt()
        fixture["same_module_local_declarations"].pop()
        with self.assertRaisesRegex(ValueError, "referenced declaration missing"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["same_module_local_declarations"].append(
            dict(fixture["same_module_local_declarations"][2]))
        with self.assertRaisesRegex(ValueError, "identity or uniqueness"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["same_module_local_declarations"].append({
            "name": DECLARATION.removesuffix(".program") + ".orphan",
            "kind": "definition", "body_scanned": True,
            "expression_nodes": 2, "immediate_symbols": [],
        })
        with self.assertRaisesRegex(ValueError, "unreachable"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["same_module_local_declarations"][0]["immediate_symbols"].append(
            DECLARATION.removesuffix(".program") + ".omitted")
        with self.assertRaisesRegex(ValueError, "root/command symbols disagree"):
            validate_kernel_root(json.dumps(fixture))

    def test_same_module_refuses_forged_theorem_erasure_and_false_external_resolution(self):
        fixture = root_receipt()
        fixture["external_module_edges_unresolved"] = False
        with self.assertRaisesRegex(ValueError, "mismatch"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        item = fixture["same_module_local_declarations"][2]
        item["kind"] = "theorem"
        with self.assertRaisesRegex(ValueError, "classification"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        item = fixture["same_module_local_declarations"][2]
        item["kind"] = "theorem"
        item["body_scanned"] = False
        with self.assertRaisesRegex(ValueError, "erasure claim|symbol list"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["same_module_local_declarations"][2]["expression_nodes"] = 8193
        with self.assertRaisesRegex(ValueError, "node budget"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["same_module_local_declarations"] = fixture["same_module_local_declarations"] * 11
        with self.assertRaisesRegex(ValueError, "declaration budget"):
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
