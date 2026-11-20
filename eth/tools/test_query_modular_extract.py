"""Fail-closed contracts for per-module original QueryStream extraction.

Offline tests exercise the orchestration boundaries; they do not fake an
original Lean import or certify source semantics.
"""
from pathlib import Path
import json
import sys
import tempfile
import unittest
from unittest.mock import patch

import query_modular_extract as q


class SourceModuleContractTests(unittest.TestCase):
    def test_stage_list_is_source_scoped_with_exact_local_abi(self):
        self.assertEqual(len(q.STAGE_BY_ID), len(q.STAGES))
        self.assertEqual(q.STAGE_BY_ID["moments_readout"].input, 15)
        self.assertEqual(q.STAGE_BY_ID["moments_readout"].output, 0)
        self.assertNotIn("QueryStreamProgram", " ".join(s.module for s in q.STAGES))
        self.assertEqual(q.STAGE_BY_ID["reconstruction"].output, 323)
        for stage in q.STAGES:
            self.assertTrue(stage.declaration.startswith("OAI.Algorithms.SubexponentialSAT."))
            self.assertTrue(stage.relative_path.as_posix().endswith(stage.module_suffix.replace(".", "/")+".lean"))

    def test_pinned_record_checks_actual_source_bytes(self):
        stage=q.STAGE_BY_ID["moments_readout"]
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            source=root/stage.relative_path
            source.parent.mkdir(parents=True)
            source.write_bytes(b"namespace Test\ndef program := compiled command 15 0\nend Test\n")
            record=q.pinned_record(stage,root)
            self.assertEqual(record["git_blob"],q.blob_hash(source.read_bytes()))
            self.assertEqual(record["module"],stage.module)
            source.write_bytes(b"def program := oracle\n")
            with self.assertRaisesRegex(ValueError, "missing expected source"):
                q.pinned_record(stage,root)

    def test_strict_abi_refuses_a_valid_graph_with_wrong_ports(self):
        stage=q.STAGE_BY_ID["moments_readout"]
        with patch.object(q,"read_source_graph",return_value=(
            b"test\n",{},object(),(8,40,17,1,14,0)
        )):
            with self.assertRaisesRegex(ValueError,"original ABI mismatch"):
                q.validate_stage_graph(Path("unused"),stage,{"id":"test"})

    @unittest.skipUnless(Path("/proc").is_dir(),"bounded process-group RSS requires Linux")
    def test_real_process_runner_accepts_normal_execution_and_refuses_failure(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            report=q.run_stage_process(
                [sys.executable,"-c","print('ok')"],root,root/"run",5
            )
            self.assertGreaterEqual(report["elapsed_ms"],0)
            self.assertEqual((root/"run.stdout.log").read_text().strip(),"ok")
            with self.assertRaisesRegex(q.Refusal,"exit 7"):
                q.run_stage_process(
                    [sys.executable,"-c","raise SystemExit(7)"],
                    root,root/"bad",5
                )
            with patch.object(q,"MAX_OUTPUT_BYTES",16):
                with self.assertRaisesRegex(q.Refusal,"bounded log budget"):
                    q.run_stage_process(
                        [sys.executable,"-c","print('x'*128)"],
                        root,root/"oversized",5
                    )
            with self.assertRaisesRegex(q.Refusal,"RSS bytes"):
                q.run_stage_process(
                    [sys.executable,"-c","import time; time.sleep(1)"],
                    root,root/"overmemory",5,rss_limit=1
                )


class ModuleReceiptContractTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.out=Path(self.temp.name)
        self.stage=q.STAGE_BY_ID["moments_readout"]
        self.record={
            "id":"query_module_moments_readout",
            "module":self.stage.module,
            "fqn":self.stage.declaration,
            "git_blob":"a"*40
        }

    def probe(self, require_cached=False):
        return q.probe_one(self.stage,self.out,self.out,self.out,
                           60,30,30,4096,q.MAX_PEAK_RSS_BYTES,
                           "Lean (version 4.34.1, x)", require_cached)

    def simulated_run(self,_argv,_cwd,log,_timeout,_rss,env=None):
        if log.name=="graph":
            (log.parent/"graph.stdout.log").write_bytes(b"source-graph\n")
            (log.parent/"graph.stderr.log").write_text(
                "SOURCE_GRAPH_PHASE=emit-complete-source-graph\n"
            )
        if log.name=="certificate":
            (log.parent/"certificate.stdout.log").write_bytes(b"")
        return {"peak_rss_bytes":100,"elapsed_ms":12}

    def test_success_is_scoped_to_kernel_checked_graph_not_rust(self):
        with (patch.object(q,"pinned_record",return_value=self.record),
              patch.object(q,"source",return_value="import Fake\n"),
              patch.object(q,"run_stage_process",side_effect=self.simulated_run),
              patch.object(q,"validate_stage_graph",return_value=(3,"b"*64)),
              patch.object(q,"certificate_source",
                           return_value=("theorem fixture : True := trivial\n",
                                         {"certificate_sha256":"c"*64}))):
            report=self.probe()
        self.assertEqual(report["status"],"ORIGINAL_MODULE_GRAPH_KERNEL_CERTIFIED")
        self.assertFalse(report["full_query"])
        self.assertEqual(report["lean_rust_refinement"],"unassessed")
        receipt=json.loads((self.out/self.stage.id/"receipt.json").read_text())
        self.assertFalse(receipt["native_executable"])
        self.assertEqual(receipt["status"],"LEAN_KERNEL_CERTIFIED_PHYSICAL_PROGRAM")
        self.assertTrue(receipt["lean_version"].startswith("Lean (version 4.34.1,"))

    def test_missing_certificate_refuses_and_clears_stale_success(self):
        stage_dir=self.out/self.stage.id
        stage_dir.mkdir()
        (stage_dir/"receipt.json").write_text("stale")
        (stage_dir/"source.json").write_text("stale")
        with (patch.object(q,"pinned_record",return_value=self.record),
              patch.object(q,"run_stage_process",side_effect=q.Refusal("blocked original module"))):
            result=self.probe()
        self.assertEqual(result["status"],"REFUSED")
        self.assertNotIn("certificate_sha256",result)
        self.assertFalse((stage_dir/"receipt.json").exists())
        self.assertFalse((stage_dir/"source.json").exists())

    def test_cache_only_refuses_without_rebuilding_original_dependency_closure(self):
        with (patch.object(q,"pinned_record",return_value=self.record),
              patch.object(q,"run_stage_process") as process):
            result=self.probe(require_cached=True)
        self.assertEqual(result["status"],"REFUSED")
        self.assertIn("compiled module missing",result["reason"])
        self.assertFalse((self.out/self.stage.id/"receipt.json").exists())
        process.assert_not_called()

    def test_cached_module_is_freshly_imported_and_never_rebuilt(self):
        module_path=(self.out/".lake/build/lib/lean"/
                     (self.stage.module.replace(".","/")+".olean"))
        module_path.parent.mkdir(parents=True,exist_ok=True)
        module_path.write_bytes(b"source-bound cached module probe")
        commands=[]
        def record(argv,cwd,log,timeout,rss,env=None):
            commands.append(argv)
            if log.name=="fresh-import":
                self.assertEqual(
                    Path(argv[-1]).read_text(),
                    f"import {self.stage.module}"+"\n",
                )
            return self.simulated_run(argv,cwd,log,timeout,rss,env)
        with (patch.object(q,"pinned_record",return_value=self.record),
              patch.object(q,"source",return_value="import Fake\n"),
              patch.object(q,"run_stage_process",side_effect=record),
              patch.object(q,"validate_stage_graph",return_value=(3,"b"*64)),
              patch.object(q,"certificate_source",
                           return_value=("theorem fixture : True := trivial\n",
                                         {"certificate_sha256":"c"*64}))):
            result=self.probe(require_cached=True)
        self.assertEqual(result["status"],"ORIGINAL_MODULE_GRAPH_KERNEL_CERTIFIED")
        self.assertEqual(result["build_mode"],"cached_module_fresh_import")
        self.assertEqual(result["cached_olean_sha256"],
                         q.hashlib.sha256(module_path.read_bytes()).hexdigest())
        self.assertTrue(commands)
        self.assertTrue(all(argv[:2] != ["lake","-K"] for argv in commands))
        self.assertEqual(commands[0][:3],["lake","env","lean"])

    def test_large_graph_is_unverified_without_unbounded_certificate(self):
        with (patch.object(q,"pinned_record",return_value=self.record),
              patch.object(q,"source",return_value="import Fake\n"),
              patch.object(q,"run_stage_process",side_effect=self.simulated_run),
              patch.object(q,"validate_stage_graph",return_value=(4097,"b"*64)),
              patch.object(q,"certificate_source") as certificate):
            result=self.probe()
        self.assertEqual(result["status"],"GRAPH_ONLY_UNCERTIFIED")
        certificate.assert_not_called()
        self.assertFalse((self.out/self.stage.id/"receipt.json").exists())


if __name__ == "__main__":
    unittest.main()
