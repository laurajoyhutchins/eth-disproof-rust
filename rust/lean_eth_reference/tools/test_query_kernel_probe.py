"""Fail-closed, offline validation of the original kernel-only root receipt."""
import json
import unittest

from query_kernel_probe import COMPILER, STATUS, validate_kernel_root
from query_stream_aot import DECLARATION


def root_receipt():
    receipt = {
        "format": "original-query-kernel-root-v5",
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
        "source_command_ir_resolved": False,
        "source_command_ir": {
            "kind": "seq",
            "first": {
                "kind": "unresolved",
                "declaration": "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.prepareHigh",
                "source_kind": "definition",
            },
            "second": {
                "kind": "seq",
                "first": {
                    "kind": "unresolved",
                    "declaration": DECLARATION.removesuffix(".program") + ".nodes",
                    "source_kind": "definition",
                },
                "second": {
                    "kind": "unresolved",
                    "declaration": "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command",
                    "source_kind": "definition",
                },
            },
        },
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
    prefix = DECLARATION.removesuffix(".program") + "."
    receipt["external_module_edges"] = [
        {
            "from": item["name"],
            "to": child,
            "target_kind": (
                "constructor"
                if child == "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq"
                else "definition"
            ),
        }
        for item in receipt["same_module_local_declarations"]
        for child in item["immediate_symbols"]
        if not child.startswith(prefix)
    ]
    targets = dict.fromkeys(edge["to"] for edge in receipt["external_module_edges"]
                            if edge["target_kind"] == "definition" and
                            edge["to"].startswith("OAI.Algorithms.SubexponentialSAT."))
    receipt["external_definition_bodies"] = [
        {
            "name": target, "kind": "definition", "status": "scanned",
            "expression_nodes": 2,
            "immediate_symbols": (
                ["Nat.zero", "OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.clearMany"]
                if i == 0 else ["Nat.zero"]
            ),
            "immediate_symbol_kinds": (
                [{"name": "Nat.zero", "kind": "constructor"},
                 {"name": "OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.clearMany",
                  "kind": "definition"}]
                if i == 0 else [{"name": "Nat.zero", "kind": "constructor"}]
            ),
            "type_status": "scanned", "type_expression_nodes": 1,
            "type_immediate_symbols": ["Nat"],
            "type_symbol_kinds": [{"name": "Nat", "kind": "inductive"}],
        } for i, target in enumerate(targets)
    ]
    receipt["second_hop_definition_bodies"] = [{
        "name": "OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.clearMany",
        "kind": "definition", "status": "scanned",
        "expression_nodes": 3, "immediate_symbols": ["Nat.zero"],
        "immediate_symbol_kinds": [{"name": "Nat.zero", "kind": "constructor"}],
        "type_status": "scanned", "type_expression_nodes": 1,
        "type_immediate_symbols": ["Nat"],
        "type_symbol_kinds": [{"name": "Nat", "kind": "inductive"}],
    }]
    return receipt


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

    def test_external_frontier_is_exact_typed_and_still_unresolved(self):
        fixture = root_receipt()
        actual = validate_kernel_root(json.dumps(fixture))
        self.assertEqual(len(actual["external_module_edges"]), 5)
        self.assertTrue(actual["external_module_edges_unresolved"])

        fixture = root_receipt()
        fixture["external_module_edges"].pop()
        with self.assertRaisesRegex(ValueError, "incomplete"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        fixture["external_module_edges"].append(dict(fixture["external_module_edges"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        fixture["external_module_edges"][0]["target_kind"] = "axiom"
        with self.assertRaisesRegex(ValueError, "disagrees"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        fixture["external_module_edges"][0]["to"] = "OAI.Forged.constant"
        with self.assertRaisesRegex(ValueError, "not in the original"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        fixture["external_module_edges"][0]["to"] = (
            DECLARATION.removesuffix(".program") + ".command"
        )
        with self.assertRaisesRegex(ValueError, "not in the original"):
            validate_kernel_root(json.dumps(fixture))

    def test_one_hop_definitions_are_exact_bounded_source_evidence(self):
        receipt = root_receipt()
        actual = validate_kernel_root(json.dumps(receipt))
        self.assertEqual(len(actual["external_definition_bodies"]), 3)
        self.assertFalse(actual["transitive_computational_closure"])

        fixture = root_receipt()
        fixture["external_definition_bodies"].pop()
        with self.assertRaisesRegex(ValueError, "coverage"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        fixture["external_definition_bodies"][0]["name"] = "OAI.Forged"
        with self.assertRaisesRegex(ValueError, "forged"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        fixture["external_definition_bodies"][1]["name"] = (
            fixture["external_definition_bodies"][0]["name"]
        )
        with self.assertRaisesRegex(ValueError, "duplicated"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        fixture["external_definition_bodies"][0]["kind"] = "theorem"
        with self.assertRaisesRegex(ValueError, "target missing"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        fixture["external_definition_bodies"][0]["expression_nodes"] = 4097
        with self.assertRaisesRegex(ValueError, "budget"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        fixture["external_definition_bodies"][0]["immediate_symbol_kinds"][0]["name"] = "OAI.Forged"
        with self.assertRaisesRegex(ValueError, "kind mismatch"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        fixture["external_definition_bodies"][0]["status"] = "node_budget_refused"
        with self.assertRaisesRegex(ValueError, "partial source symbols"):
            validate_kernel_root(json.dumps(fixture))

        fixture = root_receipt()
        refused = fixture["external_definition_bodies"][0]
        refused.update(status="node_budget_refused", expression_nodes=0,
                       immediate_symbols=[], immediate_symbol_kinds=[])
        fixture["second_hop_definition_bodies"] = []
        self.assertEqual(validate_kernel_root(json.dumps(fixture))[
            "external_definition_bodies"][0]["status"], "node_budget_refused")

        fixture = root_receipt()
        refused = fixture["external_definition_bodies"][0]
        refused.update(status="aggregate_budget_refused", expression_nodes=0,
                       immediate_symbols=[], immediate_symbol_kinds=[])
        fixture["second_hop_definition_bodies"] = []
        self.assertEqual(validate_kernel_root(json.dumps(fixture))[
            "external_definition_bodies"][0]["status"], "aggregate_budget_refused")

    def test_source_command_prefix_cannot_be_forged_or_promoted(self):
        fixture = root_receipt()
        actual = validate_kernel_root(json.dumps(fixture))
        self.assertEqual(actual["source_command_ir"]["kind"], "seq")
        self.assertFalse(actual["source_command_ir_resolved"])
        fixture = root_receipt()
        fixture["source_command_ir_resolved"] = True
        with self.assertRaisesRegex(ValueError, "mismatch"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["source_command_ir"]["first"]["declaration"] = "OAI.Forged.prepareHigh"
        with self.assertRaisesRegex(ValueError, "constructor order"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["source_command_ir"]["kind"] = "call"
        with self.assertRaisesRegex(ValueError, "constructor order"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["source_command_ir"]["second"]["first"]["kind"] = "skip"
        with self.assertRaisesRegex(ValueError, "constructor order"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["source_command_ir"]["second"]["second"]["source_kind"] = "theorem"
        with self.assertRaisesRegex(ValueError, "constructor order"):
            validate_kernel_root(json.dumps(fixture))

    def test_second_hop_is_exact_and_type_references_are_not_erasure(self):
        receipt = root_receipt()
        actual = validate_kernel_root(json.dumps(receipt))
        self.assertEqual(len(actual["second_hop_definition_bodies"]), 1)
        self.assertFalse(actual["transitive_computational_closure"])
        fixture = root_receipt()
        fixture["second_hop_definition_bodies"].clear()
        with self.assertRaisesRegex(ValueError, "coverage"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["second_hop_definition_bodies"][0]["name"] = "OAI.Forged"
        with self.assertRaisesRegex(ValueError, "forged"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["second_hop_definition_bodies"][0]["expression_nodes"] = 4097
        with self.assertRaisesRegex(ValueError, "budget"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["second_hop_definition_bodies"][0]["type_symbol_kinds"][0]["kind"] = "verified-erased"
        with self.assertRaisesRegex(ValueError, "kind mismatch"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        item = fixture["second_hop_definition_bodies"][0]
        item.update(type_status="node_budget_refused",
                    type_expression_nodes=0, type_immediate_symbols=[],
                    type_symbol_kinds=[])
        self.assertEqual(validate_kernel_root(json.dumps(fixture))[
            "second_hop_definition_bodies"][0]["type_status"], "node_budget_refused")
        fixture = root_receipt()
        item = fixture["second_hop_definition_bodies"][0]
        item["type_status"] = "node_budget_refused"
        with self.assertRaisesRegex(ValueError, "partial source symbols"):
            validate_kernel_root(json.dumps(fixture))
        fixture = root_receipt()
        fixture["external_definition_bodies"][0]["immediate_symbols"].pop()
        with self.assertRaisesRegex(ValueError, "symbol list"):
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
