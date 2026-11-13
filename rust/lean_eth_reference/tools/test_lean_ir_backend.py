#!/usr/bin/env python3
"""Offline contract tests for the compiler-IR backend adapter.

A fake lake/leanfran probes CLI handling. This is not a Lean/Rust differential
suite and does not certify the real leanfran backend.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from run_lean_ir_backend import main, validate_summary, Refusal


FAKE_LAKE = '''#!/usr/bin/env python3
import json, os, pathlib, sys
args = sys.argv[1:]
mode = os.environ.get('FAKE_BACKEND_MODE', 'ok')
if args == ['env','lean','--version']:
    print('Lean (version 4.35.0, x86_64-unknown-linux-gnu)')
elif args == ['env','leanfran','--version']:
    print('leanfran 0.6.0' if mode != 'wrong-backend' else 'leanfran 0.5.0')
elif args == ['env','leanfran','--generator-version']:
    print('4')
elif args[:4] == ['env','leanfran','module','generate']:
    if mode == 'exit-failure':
        print('simulated backend error', file=sys.stderr)
        sys.exit(254)
    module = args[args.index('--module-name')+1]
    roots = args[args.index('--roots')+1:args.index('--output-file')]
    if mode != 'empty-source':
        pathlib.Path(args[args.index('--output-file')+1]).write_text('pub fn smoke() {}\\n')
    summary = {'module': module, 'functions': 2, 'externs': 0,
               'skipped': [{'name': roots[0], 'reason': 'no compiler IR'}] if mode == 'skip' else [],
               'public': [] if mode == 'missing' else
                         [{'lean': root, 'rust': 'smoke'} for root in roots]}
    print('garbled' if mode == 'malformed' else json.dumps(summary))
else:
    print('unexpected invocation', file=sys.stderr)
    sys.exit(4)
'''


class BridgeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)
        self.lake_dir = self.dir / 'project'
        self.lake_dir.mkdir()
        (self.lake_dir / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        self.bin_dir = self.dir / 'bin'
        self.bin_dir.mkdir()
        fake_lake = self.bin_dir / 'lake'
        fake_lake.write_text(FAKE_LAKE)
        fake_lake.chmod(0o755)
        self.output = self.dir / 'generated.rs'
        self.report = self.dir / 'report.json'
        self.argv = ['--lake-root', str(self.lake_dir), '--module', 'LeanIRSmoke',
                     '--root', 'LeanIRSmoke.double', '--output-rs', str(self.output),
                     '--report', str(self.report)]

    def run_bridge(self, mode='ok'):
        with patch.dict(os.environ, {'PATH': str(self.bin_dir) + os.pathsep + os.environ['PATH'],
                                      'FAKE_BACKEND_MODE': mode}):
            return main(self.argv)

    def test_success_generates_source_and_receipt(self):
        self.assertEqual(self.run_bridge(), 0)
        self.assertEqual(self.output.read_text(), 'pub fn smoke() {}\n')
        report = json.loads(self.report.read_text())
        self.assertEqual(report['status'], 'generated-unverified')
        self.assertEqual(report['backend_summary']['public'][0]['lean'], 'LeanIRSmoke.double')
        self.assertEqual(report['semantic_verification'], 'not-established')

    def test_refuse_mismatched_lean_without_running_backend(self):
        (self.lake_dir / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
        self.assertEqual(self.run_bridge(), 2)
        self.assertFalse(self.output.exists())
        self.assertIn('silently upgrade', json.loads(self.report.read_text())['reason'])

    def test_no_partial_publication(self):
        for mode in ('wrong-backend', 'skip', 'missing', 'malformed', 'empty-source', 'exit-failure'):
            with self.subTest(mode=mode):
                if self.output.exists():
                    self.output.unlink()
                self.assertEqual(self.run_bridge(mode), 2)
                self.assertFalse(self.output.exists())
                self.assertEqual(json.loads(self.report.read_text())['status'], 'refused')

    def test_failed_second_run_does_not_replace_known_good_generated_source(self):
        self.assertEqual(self.run_bridge(), 0)
        self.assertEqual(self.run_bridge('skip'), 2)
        self.assertEqual(self.output.read_text(), 'pub fn smoke() {}\n')
        self.assertEqual(json.loads(self.report.read_text())['status'], 'refused')

    def test_reject_unsupported_root(self):
        with self.assertRaisesRegex(Refusal, 'not emitted'):
            validate_summary({'module': 'M', 'functions': 1, 'public': [], 'skipped': []},
                             'M', ['M.f'])

    def test_reject_non_declaration_inputs(self):
        self.argv[self.argv.index('--module')+1] = 'M;echo hi'
        self.assertEqual(self.run_bridge(), 2)
        self.assertFalse(self.output.exists())


if __name__ == '__main__':
    unittest.main()
