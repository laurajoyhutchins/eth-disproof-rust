"""Offline contract tests for independent pinned Lean/Rust physical traces."""
import unittest

from lean_physical_differential import (
    BASIS_SEEDS, BASIS_STEPS, lean_instruction, semantic_basis, verify_trace,
)
from verify_source_graph import KINDS, parse_instr


class PhysicalDifferentialContracts(unittest.TestCase):
    def test_only_set_accepts_a_boolean_value_operand(self):
        self.assertEqual(lean_instruction(('set', (2, 1, 3))), '.set 2 true 3')
        self.assertEqual(lean_instruction(('set', (2, 0, 3))), '.set 2 false 3')
        self.assertEqual(lean_instruction(('peek', (1, 2, 0, 3))), '.peek 1 2 0 3')
        self.assertEqual(lean_instruction(('pop', (1, 2, 0, 3))), '.pop 1 2 0 3')

    def test_synthetic_interpreter_basis_covers_entire_physical_vocabulary(self):
        basis = semantic_basis()
        r, s, labels, *_ = basis['abi']
        self.assertEqual((r, s, labels, basis['seeds'], basis['steps']),
                         (4, 3, 20, 16, 12))
        self.assertEqual({kind for kind, _ in basis['rows']}, set(KINDS))
        self.assertEqual(
            {args[1] for kind, args in basis['rows'] if kind == 'set'}, {0, 1})
        self.assertGreaterEqual(
            sum(kind == 'pop' and args[1] == args[2]
                for kind, args in basis['rows']), 2)
        self.assertGreaterEqual(
            sum(kind == 'peek' and args[1] == args[2]
                for kind, args in basis['rows']), 2)
        for row in basis['rows']:
            with self.subTest(row=row):
                # Use the same checked physical instruction decoder that
                # validates the source-exported original machine tables.
                kind, operands = parse_instr(
                    ':'.join((row[0], *(str(x) for x in row[1]))), r, s, labels)
                self.assertEqual((kind, operands), row)
                self.assertTrue(lean_instruction(row).startswith('.'))

    def test_synthetic_basis_requires_every_label_and_all_sixteen_seeds(self):
        basis = semantic_basis()
        lines = [
            f'TRACE|{basis["id"]}|{label}|{seed}|0|none|0000|,,'
            for label in range(basis['abi'][2])
            for seed in range(BASIS_SEEDS)
        ]
        self.assertEqual(
            verify_trace('\n'.join(lines), [basis]),
            {basis['id']: basis['abi'][2] * BASIS_SEEDS})
        for bad in (
            lines[:-1],
            lines + [lines[0]],
            lines[:-1] + [lines[-1].replace(
                f'|{BASIS_SEEDS - 1}|', f'|{BASIS_SEEDS}|')],
        ):
            with self.subTest(size=len(bad)), self.assertRaises(ValueError):
                verify_trace('\n'.join(bad), [basis])

    def test_missing_or_corrupt_original_lean_states_refuse(self):
        programs = [{'id': 'p', 'abi': (1, 2, 1, 0, 0, 0)}]
        good = ''.join(f'TRACE|p|0|{seed}|0|none|0|,\n' for seed in range(4))
        self.assertEqual(verify_trace(good, programs), {'p': 4})
        for bad in [good.splitlines(True)[0],
                    good + good.splitlines(True)[0],
                    good.replace('none', 'not-a-counter'),
                    good.replace('|0|,', '|7|,'),
                    good.replace('|0|,', '|0|,12'),
                    good.replace('TRACE|p', 'TRACE|q')]:
            with self.subTest(bad=bad[:55]), self.assertRaises(ValueError):
                verify_trace(bad, programs)


if __name__ == '__main__':
    unittest.main()