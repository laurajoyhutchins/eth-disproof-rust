"""Offline contract tests for independent pinned Lean/Rust physical traces."""
import unittest

from lean_physical_differential import lean_instruction, verify_trace


class PhysicalDifferentialContracts(unittest.TestCase):
    def test_only_set_accepts_a_boolean_value_operand(self):
        self.assertEqual(lean_instruction(('set', (2, 1, 3))), '.set 2 true 3')
        self.assertEqual(lean_instruction(('set', (2, 0, 3))), '.set 2 false 3')
        self.assertEqual(lean_instruction(('peek', (1, 2, 0, 3))), '.peek 1 2 0 3')
        self.assertEqual(lean_instruction(('pop', (1, 2, 0, 3))), '.pop 1 2 0 3')

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