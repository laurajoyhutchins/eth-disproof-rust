"""Fail-closed, offline validation of the original kernel-only root receipt."""
import json
import unittest

from query_kernel_probe import COMPILER, STATUS, validate_kernel_root
from query_stream_aot import DECLARATION


def root_receipt():
    receipt = {
        "format": "original-query-kernel-root-v9",
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
    # Synthetic fixture only. The original Lean probe supplies the actual
    # applied lift head and its declaration-kind evidence at runtime.
    lift = "OAI.Algorithms.SubexponentialSAT.TestFixture.liftCommand"
    reconstruction = (
        "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command"
    )
    observed = next(b for b in receipt["external_definition_bodies"]
                    if b["name"] == reconstruction)
    observed["immediate_symbols"].append(lift)
    observed["immediate_symbol_kinds"].append({"name": lift, "kind": "definition"})
    core = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.coreCommand"
    observed["immediate_symbols"].append(core)
    observed["immediate_symbol_kinds"].append({"name": core, "kind": "definition"})
    receipt["second_hop_definition_bodies"].append({
        "name": core, "kind": "definition", "status": "scanned",
        "expression_nodes": 5, "immediate_symbols": ["Nat.zero"],
        "immediate_symbol_kinds": [{"name": "Nat.zero", "kind": "constructor"}],
        "type_status": "scanned", "type_expression_nodes": 1,
        "type_immediate_symbols": ["Nat"],
        "type_symbol_kinds": [{"name": "Nat", "kind": "inductive"}],
    })
    receipt["second_hop_definition_bodies"].append({
        "name": lift, "kind": "definition", "status": "scanned",
        "expression_nodes": 2, "immediate_symbols": ["Nat.zero"],
        "immediate_symbol_kinds": [{"name": "Nat.zero", "kind": "constructor"}],
        "type_status": "scanned", "type_expression_nodes": 1,
        "type_immediate_symbols": ["Nat"],
        "type_symbol_kinds": [{"name": "Nat", "kind": "inductive"}],
    })
    def unresolved(name, kind="definition"):
        return {"kind": "unresolved", "declaration": name, "source_kind": kind}
    def seq(first, second):
        return {"kind": "seq", "first": first, "second": second}
    receipt["source_command_expanded_ir"] = seq(
        seq(
            unresolved("OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.resetHigh"),
            unresolved("OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.highCommand"),
        ),
        seq(
            seq(
                unresolved("OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.Nodes.initializeNodes"),
                seq(
                    unresolved("OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.guardCursor"),
                    unresolved(DECLARATION.removesuffix(".program") + ".nodeLoop"),
                ),
            ),
            seq(
                unresolved("OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace.handoff"),
                unresolved(lift, "application"),
            ),
        ),
    )
    lift = "OAI.Algorithms.SubexponentialSAT.TestFixture.liftCommand"
    receipt["source_lift_application"] = {
        "declaration": lift, "argument_count": 9,
        "arguments": [
            {"index": i, "head": head, "nodes": 1, "symbols": []}
            for i, head in enumerate(
                ["OfNat.ofNat"] * 4 +
                ["OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.coreCommand",
                 "OfNat.ofNat", "OfNat.ofNat", "id", "Fin.castAdd"])
        ],
        "definition_body_nodes": 6,
        "definition_body_symbols": [
            "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.call",
            "OAI.Algorithms.SubexponentialSAT.ProgramLinking.liftProgram",
            "OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled",
        ],
        "lowered_to_executable_call": False,
    }
    core = ("OAI.Algorithms.SubexponentialSAT.SqrtLogSpace."
            "QueryReconstruction.coreCommand")
    call = {
        "kind": "call",
        "program": {
            "kind": "lift", "r": 40, "s": 896,
            "registers": list(range(40)),
            "stacks": list(range(768)),
            "source": {
                "kind": "composed", "r": 40, "s": 768,
                "input": 256, "output": 323,
                "command": {
                    "kind": "unresolved",
                    "declaration": core,
                    "source_kind": "definition",
                },
            },
        },
    }
    prepare = "OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare.command"
    native = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.command"
    core_seq = {
        "kind": "seq",
        "first": {"kind": "unresolved", "declaration": prepare, "source_kind": "definition"},
        "second": {"kind": "unresolved", "declaration": native, "source_kind": "definition"},
    }
    receipt["source_core_command_ir"] = core_seq
    call["program"]["source"]["command"] = core_seq
    observed = next(b for b in receipt["second_hop_definition_bodies"]
                    if b["name"] == core)
    observed["immediate_symbols"].extend([
        "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq", prepare, native
    ])
    observed["immediate_symbol_kinds"].extend([
        {"name": "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq", "kind": "constructor"},
        {"name": prepare, "kind": "definition"},
        {"name": native, "kind": "definition"},
    ])
    receipt["source_lift_call_ir"] = call
    receipt["source_command_call_ir"] = json.loads(
        json.dumps(receipt["source_command_expanded_ir"])
    )
    receipt["source_command_call_ir"]["second"]["second"]["second"] = call
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
        with self.assertRaisesRegex(ValueError, "coverage|definition body is not observed"):
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
        fixture["second_hop_definition_bodies"] = [
            body for body in fixture["second_hop_definition_bodies"]
            if body["name"].endswith((".liftCommand", ".coreCommand"))
        ]
        self.assertEqual(validate_kernel_root(json.dumps(fixture))[
            "external_definition_bodies"][0]["status"], "node_budget_refused")

        fixture = root_receipt()
        refused = fixture["external_definition_bodies"][0]
        refused.update(status="aggregate_budget_refused", expression_nodes=0,
                       immediate_symbols=[], immediate_symbol_kinds=[])
        fixture["second_hop_definition_bodies"] = [
            body for body in fixture["second_hop_definition_bodies"]
            if body["name"].endswith((".liftCommand", ".coreCommand"))
        ]
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

    def test_lift_source_application_is_bounded_not_executable(self):
        fixture = root_receipt()
        actual = validate_kernel_root(json.dumps(fixture))
        self.assertFalse(actual["source_lift_application"]["lowered_to_executable_call"])
        for key in ("argument_count", "source_kind", "lost_compiled", "promotion"):
            with self.subTest(key=key):
                r = root_receipt()
                app = r["source_lift_application"]
                if key == "argument_count":
                    app["argument_count"] = 30
                elif key == "source_kind":
                    app["arguments"][0]["head"] = ""
                elif key == "lost_compiled":
                    app["definition_body_symbols"].pop()
                else:
                    app["lowered_to_executable_call"] = True
                with self.assertRaises(ValueError):
                    validate_kernel_root(json.dumps(r))

    def test_source_core_is_exactly_two_ordered_unresolved_commands(self):
        report = validate_kernel_root(json.dumps(root_receipt()))
        original = report["source_core_command_ir"]
        self.assertEqual(original["kind"], "seq")
        self.assertEqual(original["first"]["source_kind"], "definition")
        self.assertEqual(original["second"]["source_kind"], "definition")
        for mutation in ("swap", "skip", "forge", "extra", "promote", "evidence"):
            with self.subTest(mutation=mutation):
                report = root_receipt()
                core = report["source_core_command_ir"]
                if mutation == "swap":
                    core["first"], core["second"] = core["second"], core["first"]
                elif mutation == "skip":
                    core["first"] = {"kind": "skip"}
                elif mutation == "forge":
                    core["second"]["declaration"] = "OAI.Forged.reconstruction"
                elif mutation == "extra":
                    core["third"] = {"kind": "skip"}
                elif mutation == "promote":
                    report["source_command_ir_resolved"] = True
                else:
                    observed = next(b for b in report["second_hop_definition_bodies"]
                                    if b["name"].endswith("QueryReconstruction.coreCommand"))
                    observed["immediate_symbol_kinds"][-1]["kind"] = "theorem"
                with self.assertRaises(ValueError):
                    validate_kernel_root(json.dumps(report))

    def test_source_derived_partial_call_has_exact_finite_maps_and_refusal(self):
        report = validate_kernel_root(json.dumps(root_receipt()))
        call = report["source_lift_call_ir"]
        self.assertEqual(call["program"]["registers"], list(range(40)))
        self.assertEqual(call["program"]["stacks"], list(range(768)))
        self.assertFalse(report["rust_executable"])
        self.assertFalse(report["source_command_ir_resolved"])
        for change in ("registers", "stacks", "inner_port", "core", "call_kind",
                       "false_resolution", "applied_arg"):
            with self.subTest(change=change):
                r = root_receipt()
                p = r["source_lift_call_ir"]["program"]
                if change == "registers":
                    p["registers"][7] = 8
                elif change == "stacks":
                    p["stacks"][200] = 201
                elif change == "inner_port":
                    p["source"]["output"] = 324
                elif change == "core":
                    p["source"]["command"]["first"]["declaration"] = "OAI.Forged.prepare"
                elif change == "call_kind":
                    r["source_lift_call_ir"]["kind"] = "skip"
                elif change == "false_resolution":
                    r["source_command_ir_resolved"] = True
                else:
                    r["source_lift_application"]["arguments"][8]["head"] = "Function.const"
                with self.assertRaises(ValueError):
                    validate_kernel_root(json.dumps(r))

    def test_three_named_source_expansions_are_bound_to_original_refs(self):
        report = validate_kernel_root(json.dumps(root_receipt()))
        self.assertEqual(report["source_command_expanded_ir"]["kind"], "seq")
        self.assertFalse(report["source_command_ir_resolved"])
        for mutation in ("high", "nodes", "lift", "promotion"):
            with self.subTest(mutation=mutation):
                report = root_receipt()
                tree = report["source_command_expanded_ir"]
                if mutation == "high":
                    tree["first"]["second"]["declaration"] = "OAI.Forged.highCommand"
                elif mutation == "nodes":
                    tree["second"]["first"]["second"]["first"]["source_kind"] = "theorem"
                elif mutation == "lift":
                    tree["second"]["second"]["second"]["declaration"] = "OAI.Forged.liftCommand"
                else:
                    tree["second"]["second"]["second"]["source_kind"] = "definition"
                with self.assertRaisesRegex(ValueError, "source expanded|lift application|reconstruction"):
                    validate_kernel_root(json.dumps(report))

    def test_second_hop_is_exact_and_type_references_are_not_erasure(self):
        receipt = root_receipt()
        actual = validate_kernel_root(json.dumps(receipt))
        self.assertEqual(len(actual["second_hop_definition_bodies"]), 3)
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
