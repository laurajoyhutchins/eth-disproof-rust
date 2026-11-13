"""Real Lean (not mocked backend) tests of hash-consed elaborated Expr output."""
from __future__ import annotations
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

MODULE = Path(__file__).with_name('ResidualGraph.lean')

class LeanResidualGraphTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        lean = os.environ.get('LEAN_BIN') or shutil.which('lean')
        if not lean:
            raise AssertionError('actual Lean compiler required for real residualizer tests')
        cls.lean = lean
        cls.folder = tempfile.TemporaryDirectory(prefix='lean-residual-')
        cls.root = Path(cls.folder.name)
        shutil.copy2(MODULE, cls.root / 'ResidualGraph.lean')
        result = subprocess.run([lean, 'ResidualGraph.lean', '-o', 'ResidualGraph.olean'],
                                cwd=cls.root, env={**os.environ, 'LEAN_PATH': str(cls.root)},
                                text=True, capture_output=True, timeout=60)
        if result.returncode:
            raise AssertionError(f'actual Lean build failed: {result.stderr}\n{result.stdout}')

    @classmethod
    def tearDownClass(cls):
        if hasattr(cls, 'folder'):
            cls.folder.cleanup()

    def export(self, name: str, body: str) -> subprocess.CompletedProcess:
        path = self.root / f'{name}.lean'
        path.write_text('import ResidualGraph\n' + body + '\n', encoding='utf-8')
        return subprocess.run([self.lean, path.name], cwd=self.root,
                              env={**os.environ, 'LEAN_PATH': str(self.root)},
                              capture_output=True, text=True, timeout=45)

    def accepted(self, name: str, body: str) -> dict:
        out = self.export(name, body)
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertEqual(len(out.stdout.splitlines()), 1, out.stdout)
        result = json.loads(out.stdout)
        self.assertEqual(result['format'], 'lean-core-expr-dag-v1')
        self.assertEqual(result['status'], 'residualized-unverified')
        self.assertFalse(result['rust_executable'])
        self.assertEqual(result['physical_refinement'], 'not-established')
        self.assertTrue(result['lean_defeq_checked'])
        nodes = result['nodes']
        self.assertEqual(result['node_count'], len(nodes))
        self.assertLess(result['source_root'], len(nodes))
        self.assertLess(result['reduced_root'], len(nodes))
        for i, node in enumerate(nodes):
            for field in ('fn', 'arg', 'type', 'body', 'value', 'left', 'right'):
                if field in node and node['tag'] not in {'nat', 'string', 'const'}:
                    if type(node[field]) is int:  # Do not interpret literal fields as references.
                        self.assertLess(node[field], i, (i, node))
        return result

    def test_shared_subexpression(self):
        d = self.accepted('Shared', '''
namespace Shared
noncomputable def root : Nat → Nat := fun n => (Nat.succ (Nat.succ n)) + (Nat.succ (Nat.succ n))
end Shared
#export_residual_graph Shared.root
''')
        # Sharing is represented by repeated node references, not copied Expr trees.
        pairs = [(n.get('fn'), n.get('arg')) for n in d['nodes'] if n['tag'] == 'app']
        self.assertEqual(len(pairs), len(set(pairs)))
        # A nontrivial shared application is referenced by multiple parents.
        references = {}
        for node in d['nodes']:
            for field in ('fn', 'arg', 'type', 'body', 'value'):
                if type(node.get(field)) is int and node['tag'] not in {'nat', 'string'}:
                    child = node[field]
                    references[child] = references.get(child, 0) + 1
        self.assertTrue(any(
            count > 1 and d['nodes'][i]['tag'] == 'app'
            for i, count in references.items()))
        self.assertLess(d['node_count'], 40)

    def test_bounded_beta_zeta(self):
        d = self.accepted('Reduction', '''
namespace Reduction
noncomputable def root : Nat := (let f := (fun x : Nat => x + 1); f) 41
end Reduction
#export_residual_graph Reduction.root
''')
        self.assertEqual(d['beta_zeta_steps'], 2)
        self.assertNotEqual(d['source_root'], d['reduced_root'])

    def test_large_recursion_remains_symbolic(self):
        d = self.accepted('Large', '''
namespace Large
noncomputable def root : Nat := Nat.rec 0 (fun _ acc => acc + 1) 1000000000
end Large
#export_residual_graph Large.root
''')
        self.assertLess(d['node_count'], 100)
        self.assertIn('Nat.rec', d['source_symbols'])

    def test_axiom_refuses_without_graph(self):
        out = self.export('Axiom', '''
namespace AxiomTest
axiom oracle : Nat
noncomputable def root : Nat := oracle + 1
end AxiomTest
#export_residual_graph AxiomTest.root
''')
        self.assertNotEqual(out.returncode, 0)
        self.assertFalse(any(line.startswith('{') for line in out.stdout.splitlines()))
        self.assertIn('axiom:AxiomTest.oracle', out.stdout + out.stderr)

    def test_non_definition_refuses(self):
        out = self.export('Theorem', '''
namespace TheoremTest
theorem root : True := True.intro
end TheoremTest
#export_residual_graph TheoremTest.root
''')
        self.assertNotEqual(out.returncode, 0)
        self.assertFalse(any(line.startswith('{') for line in out.stdout.splitlines()))
        self.assertIn('not a definition', out.stdout + out.stderr)

    def test_polymorphic_universe(self):
        d = self.accepted('Polymorphic', '''
namespace Polymorphic
noncomputable def root.{u} (α : Sort u) (x : α) : α := x
end Polymorphic
#export_residual_graph Polymorphic.root
''')
        self.assertIn('param', str(d['nodes']))

    def test_unknown_root_refuses(self):
        out = self.export('Unknown', '#export_residual_graph NoSuchDefinition.ever')
        self.assertNotEqual(out.returncode, 0)
        self.assertFalse(any(line.startswith('{') for line in out.stdout.splitlines()))

if __name__ == '__main__':
    unittest.main()
