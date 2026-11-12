"""Deterministic discovery and strict original finite-table acceptance tests."""
from __future__ import annotations
import pathlib
import os
import sys
import unittest
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from extract_compiled_catalog import discover, namespaces
from export_compiled_batch import probe_source, validate_table

ROOT=pathlib.Path(os.environ.get('PINNED_ORIGINAL_SOURCE', pathlib.Path(__file__).resolve().parents[1] / 'original' / 'upstream'))

class SourceDiscoveryTests(unittest.TestCase):
    def test_original_query_closure_is_deterministic(self):
        left=discover(ROOT,True)
        right=discover(ROOT,True)
        self.assertEqual(left,right)
        self.assertEqual(left['source_commit'],'4eaee87548250b2682affda7d05d947c05554bae')
        self.assertGreaterEqual(len(left['candidates']),300)
        self.assertTrue(any(x['fqn'].endswith('QueryStreamProgram.program') for x in left['candidates']))
        self.assertFalse(any(x['fqn'].endswith('QueryStreamProgram.NO_SUCH_PROGRAM') for x in left['candidates']))

    def test_small_original_compiled_batch_is_in_query_closure(self):
        candidates=discover(ROOT,True)['candidates']
        targets={
            'OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.computeLProgram',
            'OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.logSuccProgram',
            'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram.pushProgram',
            'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram.initFrontierProgram',
            'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram.popProgram',
            'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram.popIfPresentProgram',
            'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram.pushPairProgram',
        }
        self.assertEqual({x['fqn'] for x in candidates if x['fqn'] in targets},targets)

    def test_acceptance_workflow_selects_six_original_programs(self):
        workflow=(pathlib.Path(__file__).resolve().parents[3] /
                  '.github/workflows/original-source-graph.yml').read_text()
        line=next(line for line in workflow.splitlines()
                  if line.strip().startswith('PROGRAM_REGEX: '))
        pattern=line.split("PROGRAM_REGEX: '",1)[1].rsplit("'",1)[0]
        selected=[c for c in discover(ROOT,True)['candidates']
                  if __import__('re').search(pattern,c['fqn'])]
        self.assertEqual(len(selected),6)
        self.assertNotIn(
            'OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.computeLProgram',
            {r['fqn'] for r in selected})

    def test_refuses_spoofed_program_names(self):
        rec={'module':'OAI.Algorithms.SubexponentialSAT.Foo','fqn':'OAI.Algorithms.SubexponentialSAT.Foo.program',
             'id':'foo_program_0','git_blob':'a'*40}
        probe=probe_source(rec)
        self.assertIn('#export_original_program OAI.Algorithms.SubexponentialSAT.Foo.program',probe)
        self.assertIn('set_option maxHeartbeats 2000000',probe)
        for key,value in [('fqn','Fake.unsafe'),('id','hello\"') ,('git_blob','Z'*40)]:
            altered={**rec,key:value}
            with self.assertRaises(ValueError):probe_source(altered)

    def test_source_table_fails_closed_for_corrupt_and_missing_records(self):
        rec={'id':'foo_program_0','git_blob':'a'*40}
        pin='PIN|foo_program_0|4eaee87548250b2682affda7d05d947c05554bae|'+rec['git_blob']
        rows=[pin,'PROGRAM|foo_program_0|3|2|3|0|0|1',
              'CODE|foo_program_0|0|set:0:1:1',
              'CODE|foo_program_0|1|push:1:0:2',
              'CODE|foo_program_0|2|halt',
              'END|foo_program_0|3']
        text='\n'.join(rows)+'\n'
        self.assertEqual(validate_table(text,rec,10),(3,2,3,0,0,1))
        for corrupted in (text[:-1],text+'\n',text.replace('CODE|foo_program_0|1','CODE|foo_program_0|0'),
                         text.replace('push:1:0:2','push:9:0:2'),
                         text.replace('set:0:1:1','set:0:2:1'),
                         text.replace(rec['git_blob'],'b'*40),
                         text.replace('END|foo_program_0|3','END|foo_program_0|2')):
            with self.assertRaises(ValueError):validate_table(corrupted,rec,10)

    def test_namespace_tracker_rejects_unbalanced_ends(self):
        with self.assertRaises(ValueError):namespaces('end Some\ndef program := compiled command 0 1\n',25)

if __name__ == '__main__':unittest.main()
