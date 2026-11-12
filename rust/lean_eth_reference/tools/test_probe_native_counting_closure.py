"""Bounded offline contracts for the original counting phase diagnostic."""
from pathlib import Path
import json
import tempfile
import types
import unittest
from unittest.mock import patch

from probe_native_counting_closure import (
    PHASES, PREFIX, WRAPPER_NAME, inspect, run, source_for, wrapper_for,
)
from verify_source_graph import SOURCE_SHA

BLOB = "a" * 40


def stage_graph(phase: str, width=3, cutoff=20, code=None, labels=2) -> bytes:
    _, (r, s, inp, out) = wrapper_for(phase, width, cutoff)
    return (json.dumps({
        "kind": "original-structured-source-v1",
        "source_commit": SOURCE_SHA,
        "source_blob": BLOB, "declaration": WRAPPER_NAME, "id": phase,
        "abi": {"r": r, "s": s, "labels": labels,
                "input": inp, "output": out},
        "command": code if code is not None else
            {"kind": "atom", "opcode": "set:0:1"},
    }, separators=(",", ":")) + "\n").encode("ascii")


class CountingPhaseContracts(unittest.TestCase):
    def test_each_source_stage_is_physical_with_proper_ports(self):
        expected = {
            "marked-query": (40, 896, 321, 323),
            "accepted-query": (40, 896, 700, 788),
            "local-leaf": (40, 896, 784, 788),
            "leaf": (80, 1220, 265, 263),
            "dfs": (80, 1220, 256, 256),
            "outer": (80, 1220, 256, 1216),
            "complete": (80, 1220, 256, 1216),
        }
        self.assertEqual(set(PHASES), set(expected))
        for phase, ports in expected.items():
            with self.subTest(phase=phase):
                wrapper, abi = wrapper_for(phase, 3, 20)
                self.assertEqual(abi, ports)
                self.assertIn("noncomputable def program", wrapper)
                self.assertIn("compiled (", wrapper)
                self.assertNotIn("SAT.count", wrapper)
                result = inspect(phase, stage_graph(phase), BLOB, 3, 20)
                self.assertEqual(result["abi"]["labels"], 2)
                self.assertEqual(result["status"],
                                 "SOURCE_GRAPH_STRUCTURAL_ACCEPTED_UNCERTIFIED")

    def test_full_stage_contains_real_query_leaf_dfs_and_source_entry(self):
        code, _ = wrapper_for("complete", 3, 20)
        self.assertIn("Native.entryCommand 20", code)
        self.assertIn("Native.outerCommand 3", code)
        self.assertIn("NativeLeafProgram.command 3", code)
        code, _ = wrapper_for("dfs", 3, 20)
        self.assertIn("DFSCountProgram.command 3", code)
        self.assertIn("NativeLeafProgram.command 3", code)
        code, _ = wrapper_for("marked-query", 3, 20)
        self.assertIn("HighQueryProgram.marked 3", code)

    def test_invalid_graphs_or_stage_identity_refuse(self):
        for phase in PHASES:
            with self.subTest(phase=phase):
                bad_blob = stage_graph(phase).replace(BLOB.encode(), b"b" * 40)
                with self.assertRaises(ValueError):
                    inspect(phase, bad_blob, BLOB, 3, 20)
                incorrect_abi = stage_graph(phase).replace(b'"input":', b'"input":0,"unused":')
                with self.assertRaises((KeyError, ValueError)):
                    inspect(phase, incorrect_abi, BLOB, 3, 20)
                with self.assertRaises(ValueError):
                    inspect(phase, stage_graph(phase, labels=7), BLOB, 3, 20)
        with self.assertRaises(ValueError):
            wrapper_for("semantic-oracle", 3, 20)
        with self.assertRaises(ValueError):
            wrapper_for("complete", 1, 20)

    def test_generated_probe_uses_the_one_original_source_graph_exporter(self):
        for phase in PHASES:
            wrapper, _ = wrapper_for(phase, 3, 20)
            src = source_for(wrapper, phase, BLOB, 4096)
            self.assertEqual(src.count("#export_original_source_graph " + WRAPPER_NAME + " "), 1)
            self.assertIn(WRAPPER_NAME, src)
            self.assertIn(BLOB, src)
            self.assertIn("import OAI.Algorithms.SubexponentialSAT.StructuredCalls", src)
            self.assertNotIn("def SAT.count", src)

    def test_lean_refusal_is_reported_not_promoted_to_acceptance(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            upstream = root / "upstream"
            lake = root / "lake"
            output = root / "results"
            source = upstream / ("lean/" +
                      PHASES["outer"][-1].replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True)
            source.write_text("def original := true\n")
            lake.mkdir()
            a = types.SimpleNamespace(
                upstream=upstream, lake_root=lake, output_dir=output,
                width=3, cutoff=20, max_labels=4096,
                timeout_seconds=30, phase="outer",
            )
            def fake_run(argv, **_):
                if "build" in argv:
                    return types.SimpleNamespace(returncode=0, stdout="", stderr="")
                return types.SimpleNamespace(
                    returncode=1, stdout="",
                    stderr="original source finite callee exceeds limit",
                )
            with patch("probe_native_counting_closure.ensure_pinned", return_value={}), \
                 patch("probe_native_counting_closure.subprocess.run",
                       side_effect=fake_run):
                with self.assertRaises(SystemExit):
                    run(a)
            report = json.loads((output / "counting-closure-report.json").read_text())
            self.assertFalse(report["complete_counting_verified"])
            self.assertEqual(report["accepted"], [])
            self.assertEqual(report["refused"][0]["phase"], "outer")
            self.assertEqual(report["refused"][0]["status"], "REFUSED")
            self.assertIn("finite callee", report["refused"][0]["detail"])


    def test_build_timeout_blocks_downstream_without_rebuilding(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            upstream, lake, output = root / "original", root / "lean", root / "out"
            module = PHASES["marked-query"][-1]
            source = upstream / ("lean/" + module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True)
            source.write_text("-- original source placeholder\n")
            lake.mkdir()
            calls = []
            a = types.SimpleNamespace(
                upstream=upstream, lake_root=lake, output_dir=output,
                width=3, cutoff=20, max_labels=4096,
                timeout_seconds=30, build_timeout_seconds=200,
                phase=["marked-query", "leaf", "outer", "complete"],
                no_build=False,
            )
            def slow_build(argv, **kwargs):
                calls.append(argv)
                raise __import__("subprocess").TimeoutExpired(
                    argv, kwargs["timeout"], output=b"building original OAI\n",
                    stderr=b"source closure incomplete\n",
                )
            with patch("probe_native_counting_closure.ensure_pinned", return_value={}), \
                 patch("probe_native_counting_closure.subprocess.run",
                       side_effect=slow_build):
                with self.assertRaises(SystemExit):
                    run(a)
            self.assertEqual(len(calls), 1)
            self.assertEqual(calls[0][-1], module)
            report = json.loads((output / "counting-closure-report.json").read_text())
            self.assertEqual(report["attempted"], 1)
            self.assertEqual(report["refused"][0]["phase"], "marked-query")
            self.assertIn("DEPENDENCY_BUILD_TIMEOUT",
                          report["refused"][0]["detail"])
            self.assertEqual(report["not_attempted"], ["leaf", "outer", "complete"])
            self.assertIn("source closure incomplete",
                          (output / "marked-query.build.log").read_text())
            self.assertFalse(report["complete_counting_verified"])

    def test_no_build_refuses_uncompiled_original_module_before_export(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            upstream, lake, output = root / "original", root / "lean", root / "out"
            module = PHASES["marked-query"][-1]
            source = upstream / ("lean/" + module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True)
            source.write_text("-- source placeholder\n")
            lake.mkdir()
            a = types.SimpleNamespace(
                upstream=upstream, lake_root=lake, output_dir=output,
                width=3, cutoff=20, max_labels=4096,
                timeout_seconds=30, phase=["marked-query", "leaf"], no_build=True,
            )
            with patch("probe_native_counting_closure.ensure_pinned", return_value={}), \
                 patch("probe_native_counting_closure.subprocess.run") as mock_run:
                with self.assertRaises(SystemExit):
                    run(a)
                mock_run.assert_not_called()
            report = json.loads((output / "counting-closure-report.json").read_text())
            self.assertEqual(report["not_attempted"], ["leaf"])
            self.assertIn("original .olean missing", report["refused"][0]["detail"])

    def test_imports_are_stage_scoped(self):
        from probe_native_counting_closure import phase_imports
        marked = phase_imports("marked-query")
        self.assertIn("import " + PHASES["marked-query"][-1], marked)
        self.assertNotIn("NativeOuter", marked)
        self.assertNotIn("NativeLeafProgram", marked)
        complete = phase_imports("complete")
        self.assertIn("import " + PHASES["complete"][-1], complete)
        self.assertIn("import " + PHASES["leaf"][-1], complete)



if __name__ == "__main__":
    unittest.main()
