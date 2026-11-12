"""Offline tamper and proof-reification contracts for original graph certificates."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from source_graph_kernel_certificate import certificate_source, instruction_lean

RECORD = {'id': 'sample_0', 'module': 'OAI.Algorithms.SubexponentialSAT.Example',
          'fqn': 'OAI.Algorithms.SubexponentialSAT.Example.target',
          'git_blob': 'a' * 40}


def graph():
    return {'kind': 'original-structured-source-v1',
            'source_commit': '4eaee87548250b2682affda7d05d947c05554bae',
            'source_blob': RECORD['git_blob'], 'declaration': RECORD['fqn'],
            'id': RECORD['id'],
            'abi': {'r': 2, 's': 2, 'labels': 3, 'input': 0, 'output': 1},
            'command': {'kind': 'seq',
                        'first': {'kind': 'atom', 'opcode': 'set:0:1'},
                        'second': {'kind': 'atom', 'opcode': 'pop:1:0:1'}}}


class KernelCertificateContracts(unittest.TestCase):
    def test_source_graph_reified_not_original_table(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'source.json'
            encoded = json.dumps(graph(), separators=(',', ':')).encode() + b'\n'
            p.write_bytes(encoded)
            lean, receipt = certificate_source(p, RECORD)
            self.assertEqual(receipt['physical_labels'], 3)
            self.assertEqual(receipt['source_graph_sha256'], hashlib.sha256(encoded).hexdigest())
            self.assertIn('private theorem all_steps_eq', lean)
            self.assertIn('funext pc', lean)
            self.assertIn('congrArg (fun f => cfg.pc.map f) hfun', lean)
            self.assertIn('fin_cases pc <;> rfl', lean)
            self.assertNotIn('first | rfl | decide', lean)
            self.assertIn('set_option linter.unnecessarySimpa false', lean)
            self.assertIn('Instr.halt,', lean)
            self.assertIn('Instr.set (0 : Fin 2) true (2 : Fin 3)', lean)
            self.assertIn('Instr.pop (1 : Fin 2) (0 : Fin 2) (1 : Fin 2) (0 : Fin 3)', lean)

    def test_tampered_source_identity_or_shape_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'source.json'
            original = graph()
            for update in [{'source_blob': '0' * 40},
                           {'abi': {**original['abi'], 'labels': 4}},
                           {'command': {'kind': 'atom', 'opcode': 'set:100:1'}}]:
                candidate = {**original, **update}
                p.write_bytes(json.dumps(candidate).encode() + b'\n')
                with self.subTest(update=update), self.assertRaises(ValueError):
                    certificate_source(p, RECORD)

    def test_duplicate_json_keys_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / 'source.json'
            value = json.dumps(graph())
            value = value.replace('"id": "sample_0",', '"id": "evil", "id": "sample_0",')
            p.write_text(value + '\n')
            with self.assertRaisesRegex(ValueError, 'duplicate JSON'):
                certificate_source(p, RECORD)

    def test_bool_only_for_set(self):
        self.assertEqual(instruction_lean(('set', (0, 1, 2)), 3, 2, 4),
                         'Instr.set (0 : Fin 3) true (2 : Fin 4)')
        self.assertEqual(instruction_lean(('peek', (1, 2, 0, 3)), 3, 2, 4),
                         'Instr.peek (1 : Fin 2) (2 : Fin 3) (0 : Fin 3) (3 : Fin 4)')
        with self.assertRaises(ValueError):
            instruction_lean(('peek', (2, 0, 1, 3)), 3, 2, 4)


if __name__ == '__main__':
    unittest.main()
