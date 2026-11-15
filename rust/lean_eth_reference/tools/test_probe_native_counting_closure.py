"""Bounded offline contracts for the original counting phase diagnostic."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import types
import unittest
from unittest.mock import patch

from bounded_process import run_bounded

from probe_native_counting_closure import (
    PHASES, PREFIX, WRAPPER_NAME, LARGE_FQN, LARGE_IDENTITY,
    inspect, run, source_for, wrapper_for,
)
from verify_source_graph import SOURCE_SHA

BLOB = "a" * 40


def stage_graph(phase: str, width=3, cutoff=20, code=None, labels=2) -> bytes:
    _, (r, s, inp, out) = wrapper_for(phase, width, cutoff)
    declaration = LARGE_FQN if phase == "large-domain" else WRAPPER_NAME
    identity = LARGE_IDENTITY if phase == "large-domain" else phase
    return (json.dumps({
        "kind": "original-structured-source-v1",
        "source_commit": SOURCE_SHA,
        "source_blob": BLOB, "declaration": declaration, "id": identity,
        "abi": {"r": r, "s": s, "labels": labels,
                "input": inp, "output": out},
        "command": code if code is not None else
            {"kind": "atom", "opcode": "set:0:1"},
    }, separators=(",", ":")) + "\n").encode("ascii")


class CountingPhaseContracts(unittest.TestCase):
    @unittest.skipUnless(os.name == "posix", "POSIX process groups required")
    def test_completed_bounded_process_preserves_lean_logs(self):
        with tempfile.TemporaryDirectory() as tmp:
            completed = run_bounded(
                ["sh", "-c", 'printf ready; printf warning >&2'],
                cwd=Path(tmp), timeout=3,
            )
            self.assertEqual(completed.returncode, 0)
            self.assertEqual(completed.stdout, "ready")
            self.assertEqual(completed.stderr, "warning")

    @unittest.skipUnless(os.name == "posix", "POSIX process groups required")
    def test_timed_out_lake_like_parent_cannot_leave_live_cache_writers(self):
        # A shell child inheriting Lake's group attempts to change an artifact
        # after the parent's timeout. The process group must be hard-killed.
        # Use POSIX sh rather than Python startup to make this test quick.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            marker = root / "late-olean"
            shell = (
                '(sleep 0.5; printf leaked > "$1") & '
                'printf "child started\\n"; sleep 10'
            )
            with self.assertRaises(subprocess.TimeoutExpired) as captured:
                run_bounded(
                    ["sh", "-c", shell, "sh", str(marker)],
                    cwd=root, timeout=0.15,
                )
            self.assertIn(b"child started", captured.exception.stdout or b"")
            time.sleep(0.7)
            self.assertFalse(marker.exists(), "orphan process modified cached output")

    def test_each_source_stage_is_physical_with_proper_ports(self):
        expected = {
            "marked-query": (40, 896, 321, 323),
            "accepted-query": (40, 896, 700, 788),
            "local-leaf": (40, 896, 784, 788),
            "leaf": (80, 1220, 265, 263),
            "dfs": (80, 1220, 256, 256),
            "outer": (80, 1220, 256, 1216),
            "complete": (80, 1220, 256, 1216),
            "large-domain": (80, 1220, 256, 1216),
        }
        self.assertEqual(set(PHASES), set(expected))
        for phase, ports in expected.items():
            with self.subTest(phase=phase):
                wrapper, abi = wrapper_for(phase, 3, 20)
                self.assertEqual(abi, ports)
                declaration = "largeOnlyProgram" if phase == "large-domain" else "program"
                self.assertIn("noncomputable def " + declaration, wrapper)
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
        large, _ = wrapper_for("large-domain", 3, 20)
        self.assertIn("Native.outerCommand 3 (NativeLeafProgram.command 3)", large)
        self.assertIn("FiniteFallback.cutoffCommand 20", large)
        self.assertNotIn("FiniteFallback.framedCommand 20", large)

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

    def test_source_graph_total_labels_have_separate_finite_callee_limit(self):
        from run_source_graph_batch import LEAN
        from verify_source_graph import MAX_SOURCE_LABELS
        self.assertEqual(MAX_SOURCE_LABELS, 50_000)
        exporter = LEAN.read_text()
        self.assertIn('private def maxSourceLabels : Nat := 50000', exporter)
        self.assertIn('labels > maxSourceLabels', exporter)
        self.assertIn('l > maxSourceLabels', exporter)
        # Finite leaf materialization remains bounded independently.
        self.assertIn("l > maxLabels", exporter)
        self.assertIn("ORIGINAL_MAX_LABELS must be 1..8192", exporter)
    def test_generated_probe_uses_the_one_original_source_graph_exporter(self):
        for phase in PHASES:
            wrapper, _ = wrapper_for(phase, 3, 20)
            src = source_for(wrapper, phase, BLOB, 4096)
            decl = LARGE_FQN if phase == "large-domain" else WRAPPER_NAME
            self.assertEqual(src.count("#export_original_source_graph " + decl + " "), 1)
            self.assertIn(decl, src)
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
                 patch("probe_native_counting_closure.run_bounded",
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
                 patch("probe_native_counting_closure.run_bounded",
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
                 patch("probe_native_counting_closure.run_bounded") as mock_run:
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
        self.assertEqual(phase_imports("large-domain"), phase_imports("complete"))
        complete = phase_imports("complete")
        self.assertIn("import " + PHASES["complete"][-1], complete)
        self.assertIn("import " + PHASES["leaf"][-1], complete)



    def test_two_queries_share_one_successful_original_module_build(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            upstream, lake, output = root / "original", root / "lean", root / "out"
            module = PHASES["marked-query"][-1]
            source = upstream / ("lean/" + module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True)
            source.write_text("-- pinned fixture source\n")
            lake.mkdir()
            calls = []
            a = types.SimpleNamespace(
                upstream=upstream, lake_root=lake, output_dir=output,
                width=3, cutoff=20, max_labels=4096,
                timeout_seconds=30, build_timeout_seconds=60,
                phase=["marked-query", "accepted-query"], no_build=False,
            )
            def fake_run(argv, **kwargs):
                calls.append(argv)
                if "build" in argv:
                    return types.SimpleNamespace(
                        returncode=0, stdout="build complete", stderr="")
                probe_text = Path(argv[-1]).read_text()
                phase = "marked-query" if '"marked-query"' in probe_text else "accepted-query"
                return types.SimpleNamespace(
                    returncode=0, stdout=stage_graph(phase).decode(), stderr="")
            with patch("probe_native_counting_closure.ensure_pinned", return_value={}), \
                 patch("probe_native_counting_closure.blob_hash", return_value=BLOB), \
                 patch("probe_native_counting_closure.run_bounded",
                       side_effect=fake_run):
                result = run(a)
            self.assertEqual(len([argv for argv in calls if "build" in argv]), 1)
            self.assertEqual(len(result["accepted"]), 2)
            self.assertEqual(result["refused"], [])
            report = json.loads((output / "counting-closure-report.json").read_text())
            self.assertEqual(report["attempted"], 2)
            self.assertEqual(report["not_attempted"], [])
            self.assertFalse(report["complete_counting_verified"])



if __name__ == "__main__":
    unittest.main()
