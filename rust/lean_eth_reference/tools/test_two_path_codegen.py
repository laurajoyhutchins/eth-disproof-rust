"""Routing/refusal contract tests; neither backend is certified by mocks."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from run_two_path_codegen import main
from test_lean_codegen_contract import ir_report, residual


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        for args in [('init', '-q'), ('config', 'user.name', 'Test'),
                     ('config', 'user.email', 'test@example.org')]:
            subprocess.run(['git', '-C', str(self.repo), *args], check=True)
        (self.repo / 'Demo.lean').write_text('namespace Demo\ndef double (n : Nat) := n + n\nend Demo\n')
        (self.repo / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        subprocess.run(['git', '-C', str(self.repo), 'add', '.'], check=True)
        subprocess.run(['git', '-C', str(self.repo), 'commit', '-qm', 'pin'], check=True)
        self.rev = subprocess.check_output(['git', '-C', str(self.repo), 'rev-parse', 'HEAD'],
                                           text=True).strip()
        self.artifact = self.repo / 'result.bin'
        self.receipt = self.repo / 'receipt.json'
        self.args = ['--backend', 'compiler-ir', '--lake-root', str(self.repo),
                     '--module', 'Demo', '--root', 'Demo.double', '--source-repo', str(self.repo),
                     '--source-path', 'Demo.lean', '--source-revision', self.rev,
                     '--output', str(self.artifact), '--receipt', str(self.receipt)]

    @staticmethod
    def fake_generator(argv):
        def arg(flag): return Path(argv[argv.index(flag)+1])
        code = b'pub fn double() {}\n'
        arg('--output-rs').write_bytes(code)
        arg('--report').write_bytes(ir_report(code))
        return 0

    def test_ir_success_remains_unverified(self):
        with patch('run_two_path_codegen.run_ir', side_effect=self.fake_generator):
            self.assertEqual(main(self.args), 0)
        self.assertEqual(json.loads(self.receipt.read_text())['status'], 'generated-unverified')
        self.assertFalse(json.loads(self.receipt.read_text())['executable_approved'])

    def test_ir_refusal_does_not_automatically_use_symbolic(self):
        with patch('run_two_path_codegen.run_ir', return_value=2) as ir, \
             patch('run_two_path_codegen.symbolic') as sym:
            self.assertEqual(main(self.args), 2)
        ir.assert_called_once()
        sym.assert_not_called()
        self.assertFalse(self.artifact.exists())
        self.assertFalse(self.receipt.exists())

    def test_recheck_source_after_generation(self):
        def changing(argv):
            result = self.fake_generator(argv)
            (self.repo / 'Demo.lean').write_text('namespace Demo\nend Demo\n')
            return result
        with patch('run_two_path_codegen.run_ir', side_effect=changing):
            self.assertEqual(main(self.args), 2)
        self.assertFalse(self.receipt.exists())
        self.assertFalse(self.artifact.exists())

    def test_symbolic_route_uses_same_contract(self):
        params = self.args.copy()
        params[params.index('--backend')+1] = 'residual-expr'
        with patch('run_two_path_codegen.symbolic', return_value=(residual(), 'a'*64)):
            self.assertEqual(main(params), 0)
        info = json.loads(self.receipt.read_text())
        self.assertEqual(info['status'], 'residualized-unverified')
        self.assertEqual(info['producer_sha256'], 'a'*64)
        self.assertFalse(info['executable_approved'])

    def test_failed_second_attempt_invalidates_old_receipt(self):
        with patch('run_two_path_codegen.run_ir', side_effect=self.fake_generator):
            self.assertEqual(main(self.args), 0)
        with patch('run_two_path_codegen.run_ir', return_value=2):
            self.assertEqual(main(self.args), 2)
        self.assertFalse(self.receipt.exists())


if __name__ == '__main__':
    unittest.main()
