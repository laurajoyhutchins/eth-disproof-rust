"""Admission tests for the shared Rust-data -> source-checked Lean renderer.

These tests intentionally do not call a parser result a proof. The pinned
Lean kernel gate must reject tables with the wrong physical instructions.
"""
from __future__ import annotations

import copy
import json
import unittest

from verify_rust_physical_receipt import CASES, certificate_source
from verify_source_graph import SOURCE_SHA


def sample() -> dict:
    cases = []
    for name, (r, s, tag, present, found, source, payload, inp, out) in CASES.items():
        def table(labels, input_port, output_port):
            return {
                'r': r, 's': s, 'labels': labels, 'entry': 0,
                'input': input_port, 'output': output_port,
                'code': ['halt'] * labels,
            }
        cases.append({
            'name': name,
            'ports': dict(zip(
                ('tag', 'present', 'found', 'source', 'payload', 'input', 'output'),
                (tag, present, found, source, payload, inp, out))),
            'lifted': table(7, source, payload),
            'compiled': table(8, inp, out),
        })
    return {'kind': 'rust-physical-programs-v1',
            'source_commit': SOURCE_SHA, 'cases': cases}


def encode(value: dict) -> bytes:
    return (json.dumps(value, separators=(',', ':')) + '\n').encode('ascii')


class RustPhysicalReceiptTests(unittest.TestCase):
    def test_parser_reuses_the_original_source_table_lean_renderer(self):
        text = certificate_source(encode(sample()))
        self.assertIn('private def rust_lift_dedup : Program 15 16 7', text)
        self.assertIn('private def rust_compiled_reversal : Program 3 4 8', text)
        self.assertIn('Instr.halt', text)
        self.assertEqual(text.count('private theorem rust_compiled_'), 6)
        self.assertEqual(text.count('theorem rust_compiled_'), 12)

    def test_invalid_source_pin_and_duplicate_receipts_refuse(self):
        for mutate in (
            lambda a: a.update(source_commit='0' * 40),
            lambda a: a['cases'].pop(),
            lambda a: a['cases'][1].update(name='dedup'),
            lambda a: a['cases'][0]['ports'].update(found=0),
            lambda a: a['cases'][0]['lifted']['code'].pop(),
            lambda a: a['cases'][0]['compiled']['code'].__setitem__(0, 'unknown'),
            lambda a: a['cases'][0]['compiled']['code'].__setitem__(0, 'goto:8'),
            lambda a: a['cases'][0]['compiled'].update(entry=8),
            lambda a: a['cases'][0]['compiled'].update(extra=1),
        ):
            with self.subTest(mutate=mutate):
                value = sample()
                mutate(value)
                with self.assertRaises((ValueError, KeyError, TypeError)):
                    certificate_source(encode(value))

    def test_ambiguous_json_and_noncanonical_lines_refuse(self):
        example = encode(sample())
        bad = [
            example[:-1],
            example + b'{}\n',
            example.replace(b'"kind":', b'"kind":"other","kind":', 1),
        ]
        for raw in bad:
            with self.subTest(raw=raw[:65]):
                with self.assertRaises((ValueError, KeyError)):
                    certificate_source(raw)

    def test_instruction_mutation_changes_kernel_submission_not_parser_proof(self):
        base = sample()
        altered = copy.deepcopy(base)
        altered['cases'][0]['compiled']['code'][1] = 'pop:13:1:0:2'
        assert certificate_source(encode(base)) != certificate_source(encode(altered))
        # Both receipts *parse*. Only the pinned Lean checker determines
        # whether the emitted physical table equals the original source.


if __name__ == '__main__':
    unittest.main()
