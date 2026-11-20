"""Admission tests for the shared Rust-data -> source-checked Lean renderer.

These tests intentionally do not call a parser result a proof. The pinned
Lean kernel gate must reject tables with the wrong physical instructions.
"""
from __future__ import annotations

import copy
import json
import unittest

from verify_rust_physical_receipt import (
    CASES, FIELD_PROOF, FRAMED_PROOF, certificate_source,
    preflight_proof_dependencies,
)
from verify_source_graph import FIELDS, RUST_NAMES, SOURCE_SHA


# Fixture construction is separate from the production Rust encoder.
# This code does not determine source identity or kernel acceptance.
def derived(table: dict) -> dict:
    typed = []
    for row in table['code']:
        opcode, *arguments = row.split(':')
        if opcode == 'halt':
            typed.append('Halt')
        else:
            fields = {}
            for field, number in zip(FIELDS[opcode], arguments):
                fields[field] = bool(int(number)) if opcode == 'set' and field == 'value' else int(number)
            typed.append({RUST_NAMES[opcode]: fields})
    return {
        'input_stack': table['input'],
        'output_stack': table['output'],
        'entry': table['entry'],
        'code': typed,
    }


def sample() -> dict:
    cases = []
    for name, (r, s, tag, present, found, source, payload, inp, out) in CASES.items():
        def table(labels, input_port, output_port):
            return {
                'r': r, 's': s, 'labels': labels, 'entry': 0,
                'input': input_port, 'output': output_port,
                'code': ['halt'] * labels,
            }
        lifted = table(7, source, payload)
        compiled = table(8, inp, out)
        cases.append({
            'name': name,
            'ports': dict(zip(
                ('tag', 'present', 'found', 'source', 'payload', 'input', 'output'),
                (tag, present, found, source, payload, inp, out))),
            'lifted': lifted,
            'compiled': compiled,
            'structure': {'lifted': derived(lifted), 'compiled': derived(compiled)},
        })
    corpus = {
        'r': 4, 's': 3, 'labels': 13, 'entry': 0,
        'input': 0, 'output': 1,
        'code': [
            'halt', 'goto:0', 'set:0:1:1', 'set:1:0:2',
            'copy:0:1:2', 'not:1:2:3', 'and:0:1:2:4',
            'or:1:2:3:5', 'xor:2:3:0:6', 'branch:3:0:12',
            'push:2:3:7', 'peek:1:2:3:8', 'pop:2:1:0:9',
        ],
    }
    return {
        'kind': 'rust-physical-programs-v2',
        'source_commit': SOURCE_SHA,
        'encoding_corpus': {'physical': corpus, 'structure': derived(corpus)},
        'cases': cases,
    }


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
        self.assertEqual(text.count('apply ACC.BitProgramFields.eq_of_fields'), 12)
        self.assertNotIn('apply program_eq_of_fields', text)

    def test_generated_proof_dependencies_fail_before_lean(self):
        generated = certificate_source(encode(sample()))
        framed = FRAMED_PROOF.read_text(encoding='utf-8')
        shared = FIELD_PROOF.read_text(encoding='utf-8')
        preflight_proof_dependencies(generated, framed, shared)

        mutants = (
            ('deleted import',
             generated, framed.replace('import ACC.BitProgramFields',
                                       'import ACC.MissingFields'), shared),
            ('renamed shared namespace',
             generated, framed,
             shared.replace('namespace ACC.BitProgramFields',
                            'namespace ACC.ObsoleteFields', 1)),
            ('deleted shared theorem',
             generated, framed,
             shared.replace('theorem eq_of_fields', 'theorem renamed_fields', 1)),
            ('stale handwritten proof application',
             generated,
             framed.replace('  apply ACC.BitProgramFields.eq_of_fields',
                            '  apply program_eq_of_fields', 1),
             shared),
            ('deleted framed source theorem',
             generated,
             framed.replace('theorem mappedCompiledFrameProgram_eq_source',
                            'theorem removed_compiled_source', 1),
             shared),
            ('stale generated proof application',
             generated.replace('  apply ACC.BitProgramFields.eq_of_fields',
                               '  apply program_eq_of_fields', 1),
             framed, shared),
            ('stale generated rewrite consumer',
             generated.replace(', mappedFrameProgram_eq_source]',
                               ', removed_frame_source]', 1),
             framed, shared),
        )
        for name, code, source, lemma in mutants:
            with self.subTest(name=name), self.assertRaises(ValueError):
                preflight_proof_dependencies(code, source, lemma)

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
            lambda a: a.update(kind='rust-physical-programs-v1'),
            lambda a: a.pop('encoding_corpus'),
            lambda a: a['encoding_corpus']['physical']['code'].pop(),
            lambda a: a['encoding_corpus']['structure']['code'].__setitem__(0, 'Goto'),
            lambda a: a['cases'][0]['structure']['lifted'].update(input_stack=0),
            lambda a: a['cases'][0]['structure']['compiled']['code'].pop(1),
            lambda a: a['cases'][0]['structure']['compiled']['code'].__setitem__(0, 'Goto'),
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

    def test_every_opcode_and_operand_is_covered_by_structural_mismatch_checks(self):
        original = sample()
        data = original['encoding_corpus']['structure']['code']
        for index, typed in enumerate(data):
            if index == 0:
                changed = copy.deepcopy(original)
                changed['encoding_corpus']['structure']['code'][0] = 'Goto'
                with self.subTest(index=index, field='variant'):
                    with self.assertRaises(ValueError):
                        certificate_source(encode(changed))
                continue
            name, fields = next(iter(typed.items()))
            for field, value in fields.items():
                changed = copy.deepcopy(original)
                target = changed['encoding_corpus']['structure']['code'][index][name]
                target[field] = not value if type(value) is bool else value + 1
                with self.subTest(index=index, field=field):
                    with self.assertRaises(ValueError):
                        certificate_source(encode(changed))

    def test_row_only_mutation_refused_before_lean(self):
        changed = sample()
        changed['cases'][0]['compiled']['code'][1] = 'pop:13:1:0:2'
        with self.assertRaises(ValueError):
            certificate_source(encode(changed))

    def test_consistent_but_wrong_source_program_requires_lean_rejection(self):
        # A second encoder is a consistency oracle, not source correctness.
        base = sample()
        altered = copy.deepcopy(base)
        altered['cases'][0]['compiled']['code'][1] = 'goto:0'
        altered['cases'][0]['structure']['compiled']['code'][1] = {'Goto': {'next': 0}}
        assert certificate_source(encode(base)) != certificate_source(encode(altered))
        # Both receipts parse. Only the pinned Lean kernel can decide
        # whether a changed, internally consistent program matches source.


if __name__ == '__main__':
    unittest.main()
