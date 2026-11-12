"""Offline structural graph validity tests, independent of pinned Lean availability."""
import hashlib
import json
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from verify_source_graph import (
    SOURCE_SHA, Node, parse_instr, parse_node, parse_program, generate_test, rust_instr,
    parse_golden, parse_source_graph_json, validate_and_generate,
)


class GraphContracts(unittest.TestCase):
    def test_register_value_is_not_a_bool_in_peek_or_pop(self):
        # 'value' names a register in these instructions, unlike .set.
        self.assertEqual(
            rust_instr(('peek', (1, 2, 0, 3))),
            'Instr::Peek { stack: 1, value: 2, present: 0, next: 3 }')
        self.assertEqual(
            rust_instr(('pop', (1, 2, 0, 3))),
            'Instr::Pop { stack: 1, value: 2, present: 0, next: 3 }')
        self.assertEqual(
            rust_instr(('set', (2, 1, 3))),
            'Instr::Set { dst: 2, value: true, next: 3 }')
        self.assertEqual(
            rust_instr(('set', (2, 0, 3))),
            'Instr::Set { dst: 2, value: false, next: 3 }')

    def test_simple_sequence_exact_physical_layout(self):
        cmd = {'kind':'seq',
               'first':{'kind':'atom','opcode':'set:0:1'},
               'second':{'kind':'while','test':0,
                         'body':{'kind':'atom','opcode':'set:0:0'}}}
        root=parse_node(cmd,2,2,[8192])
        self.assertEqual(root.size,3)
        self.assertEqual(root.entry(1,0),1)
        self.assertEqual(root.instr(1,0,1),('set',(0,1,2)))
        self.assertEqual(root.instr(1,0,2),('branch',(0,3,0)))
        self.assertEqual(root.instr(1,0,3),('set',(0,0,2)))

    def test_source_call_relocates_halt_and_every_branch(self):
        program={'r':2,'s':2,'labels':3,'input':0,'output':1,'entry':2,
                 'code':['halt','goto:0','set:0:1:1']}
        root=parse_node({'kind':'seq','first':{'kind':'call','program':program},
                         'second':{'kind':'atom','opcode':'set:1:1'}},2,2,[8192])
        self.assertEqual(root.size,4)
        self.assertEqual(root.entry(1,0),3)
        self.assertEqual(root.instr(1,0,1),('goto',(4,)))
        self.assertEqual(root.instr(1,0,2),('goto',(1,)))
        self.assertEqual(root.instr(1,0,3),('set',(0,1,2)))
        self.assertEqual(root.instr(1,0,4),('set',(1,1,0)))

    def test_unknown_constructor_and_bad_indices_refuse(self):
        for cmd in [
            {'kind':'semantic_sat_oracle'},
            {'kind':'atom','opcode':'push:2:0'},
            {'kind':'if','test':2,'yes':{'kind':'skip'},'no':{'kind':'skip'}},
            {'kind':'while','test':0,'body':{'kind':'unsupported'}},
            {'kind':'seq','first':{'kind':'skip'},'second':{'kind':'skip'},'extra':'ignored'},
            {'kind':'call','program':{'r':2,'s':2,'labels':2,'entry':0,
                                      'input':0,'output':1,'code':['halt']}},
        ]:
            with self.subTest(cmd=cmd), self.assertRaises(ValueError):
                parse_node(cmd,2,2,[8192])
        for bad in ['set:00:1:0','set:0:5:0','goto:-1','halt:0','peek:0:0:1:5']:
            with self.subTest(instr=bad), self.assertRaises(ValueError):
                parse_instr(bad,2,2,2)

    def test_repeated_source_calls_keep_exact_physical_site_layout(self):
        program = {'r':2,'s':2,'labels':3,'input':0,'output':1,'entry':2,
                   'code':['halt','goto:0','set:0:1:1']}
        call = {'kind':'call','program':program}
        command = {'kind':'seq','first':call,'second':
                   {'kind':'seq','first':call,'second':call}}
        root = parse_node(command,2,2,[8192])
        self.assertEqual(root.size,9)
        self.assertEqual(root.entry(1,0),3)
        self.assertEqual(root.instr(1,0,3),('set',(0,1,2)))
        self.assertEqual(root.instr(1,0,6),('set',(0,1,5)))
        self.assertEqual(root.instr(1,0,9),('set',(0,1,8)))

    def test_program_identity_includes_ports_not_only_instruction_bytes(self):
        program = {'r':2,'s':2,'labels':2,'input':0,'output':1,'entry':1,
                   'code':['halt','goto:0']}
        changed = {**program, 'output':0}
        a = parse_program(program,[8192])
        b = parse_program(changed,[8192])
        self.assertNotEqual(a.key(), b.key())
        self.assertEqual(a.instruction(1), b.instruction(1))

    def test_lift_remaps_all_twelve_original_physical_opcodes(self):
        program={'r':4,'s':3,'labels':12,'entry':1,'input':0,'output':2,
                 'code':['halt','goto:11','set:0:1:3','copy:1:2:4',
                         'not:3:1:5','and:0:1:2:6','or:2:3:1:7',
                         'xor:1:0:3:8','branch:2:9:10','push:1:0:11',
                         'peek:0:3:2:11','pop:2:1:3:0']}
        lifted={'kind':'lift','r':6,'s':5,'registers':[5,1,3,0],
                'stacks':[4,2,1],'source':program}
        parsed=parse_program(lifted,[8192])
        self.assertEqual((parsed.entry,parsed.input,parsed.output),(1,4,1))
        self.assertEqual([parsed.instruction(pc) for pc in range(12)],[
            ('halt',()), ('goto',(11,)), ('set',(5,1,3)),
            ('copy',(1,3,4)), ('not',(0,1,5)), ('and',(5,1,3,6)),
            ('or',(3,0,1,7)), ('xor',(1,5,0,8)),
            ('branch',(3,9,10)), ('push',(2,5,11)),
            ('peek',(4,0,3,11)), ('pop',(1,1,0,0)),
        ])

    def test_linked_lean_physical_layout_and_source_graph(self):
        left = {'r':2,'s':2,'labels':3,'entry':2,'input':0,'output':1,
                'code':['halt','goto:0','set:0:1:1']}
        right = {'r':2,'s':2,'labels':2,'entry':1,'input':0,'output':1,
                 'code':['halt','push:1:0:0']}
        linked = {'kind':'link','left':left,'right':right}
        lifted = {'kind':'lift','r':3,'s':4,'registers':[2,0],
                  'stacks':[3,1],'source':linked}
        root = parse_node({'kind':'call','program':lifted},3,4,[8192])
        self.assertEqual(root.size,5)
        self.assertEqual(root.entry(1,0),3)
        self.assertEqual([root.instr(1,0,pc) for pc in range(1,6)], [
            ('goto',(5,)), ('goto',(1,)), ('set',(2,1,2)),
            ('goto',(0,)), ('push',(1,2,4)),
        ])

    def test_link_into_distinct_physical_port_dimensions(self):
        left = {'r':2,'s':1,'labels':2,'entry':1,'input':0,'output':0,
                'code':['halt','set:0:1:0']}
        right = {'r':1,'s':2,'labels':2,'entry':1,'input':0,'output':1,
                 'code':['halt','push:1:0:0']}
        link = {'kind':'link_into','r':3,'s':4,
                'left':left,'right':right,
                'left_registers':[2,0],'left_stacks':[3],
                'right_registers':[1],'right_stacks':[0,2]}
        root = parse_node({'kind':'call','program':link},3,4,[8192])
        self.assertEqual(root.args['input'],3)
        self.assertEqual(root.args['output'],2)
        self.assertEqual(root.entry(1,0),2)
        self.assertEqual([root.instr(1,0,pc) for pc in range(1,5)], [
            ('goto',(4,)), ('set',(2,1,1)), ('goto',(0,)),
            ('push',(2,1,3)),
        ])

    def test_linked_graph_invalid_map_or_dimensions_refuse(self):
        table = {'r':2,'s':2,'labels':2,'entry':1,'input':0,'output':1,
                 'code':['halt','set:0:1:0']}
        for bad in [
            {'kind':'lift','r':3,'s':3,'registers':[0,0],
             'stacks':[0,1],'source':table},
            {'kind':'lift','r':3,'s':3,'registers':[0,3],
             'stacks':[0,1],'source':table},
            {'kind':'lift','r':3,'s':3,'registers':[0],
             'stacks':[0,1],'source':table},
            {'kind':'lift','r':3,'s':3,'registers':[0,1],
             'stacks':[0,0],'source':table},
            {'kind':'link','left':table,'right':{**table,'r':3,'code':['halt','set:0:1:0']}},
            {'kind':'link_into','r':3,'s':3,'left':table,'right':table,
             'left_registers':[0,1],'left_stacks':[0,1],
             'right_registers':[0,1],'right_stacks':[1,1]},
            {'kind':'table','r':2,'s':2,'labels':2,'entry':1,'input':0,'output':1,
             'code':['halt','set:0:1:0']},
        ]:
            with self.subTest(bad=bad),self.assertRaises(ValueError):
                parse_node({'kind':'call','program':bad},3,3,[8192])

    def test_generator_rejects_ambiguous_serialized_graphs(self):
        # These must match the kernel-certificate input requirements.
        malformed = [
            b'{"id":"first","id":"second"}\n',
            b'{"command":{"kind":"atom","kind":"skip"}}\n',
            b'{"value":NaN}\n',
            b'{"value":Infinity}\n',
            b'[]\n',
            b'{"value":1}\n{"value":2}\n',
            b'{"value":1}',
            '{"value":"μ"}\n'.encode('utf-8'),
        ]
        for raw in malformed:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                parse_source_graph_json(raw)
        self.assertEqual(parse_source_graph_json(b'{"value":1}\n'), {'value': 1})

    def test_pin_hash_and_exact_program_equality(self):
        ident='small_0'
        blob='1'*40
        raw=(f'PIN|{ident}|{SOURCE_SHA}|{blob}\n'
             f'PROGRAM|{ident}|2|2|2|1|0|1\n'
             f'CODE|{ident}|0|halt\n'
             f'CODE|{ident}|1|set:0:1:0\n'
             f'END|{ident}|2\n').encode()
        with tempfile.TemporaryDirectory() as scratch:
            root=Path(scratch)
            golden=root/'golden';golden.mkdir()
            (golden/(ident+'.table')).write_bytes(raw)
            manifest={ident:{'source_blob':blob,'sha256':hashlib.sha256(raw).hexdigest(),
                             'declaration':'OAI.Algorithms.SubexponentialSAT.T.small'}}
            (golden/'manifest.json').write_text(json.dumps(manifest))
            graph={'kind':'original-structured-source-v1', 'source_commit':SOURCE_SHA,
                   'source_blob':blob, 'declaration':manifest[ident]['declaration'],
                   'id':ident,'abi':{'r':2,'s':2,'labels':2,'input':0,'output':1},
                   'command':{'kind':'atom','opcode':'set:0:1'}}
            inp=root/'graph.json'
            inp.write_text(json.dumps(graph)+'\n')
            receipt=validate_and_generate(inp,golden,root/'out',root,False)
            self.assertEqual(receipt['physical_instructions_compared'],2)
            self.assertEqual(receipt['rust_loader'], 'original-structured-source-v1/serde-native')
            self.assertIn('from_original_source_json(include_bytes!("source.json")',
                          (root/'out'/(ident+'.rs')).read_text())
            self.assertTrue((root/'out'/(ident+'.rs')).exists())
            # A failed Rust compile invalidates an earlier successful receipt.
            rust_path=root/'out'/(ident+'.rs')
            receipt_path=root/'out'/(ident+'.receipt.json')
            saved_rust=rust_path.read_text()
            self.assertTrue(receipt_path.exists())

            def failed_build(command, **kwargs):
                manifest_path=Path(command[-1])
                self.assertTrue(manifest_path.is_file())
                self.assertTrue((manifest_path.parent/'tests/source.rs').is_file())
                self.assertFalse(receipt_path.exists())
                return subprocess.CompletedProcess(command, 1, stdout='', stderr='intentional compile failure')

            with patch('verify_source_graph.subprocess.run', side_effect=failed_build):
                with self.assertRaisesRegex(RuntimeError, 'intentional compile failure'):
                    validate_and_generate(inp,golden,root/'out',root,True)
            self.assertFalse(receipt_path.exists())
            self.assertEqual(rust_path.read_text(),saved_rust)
            self.assertEqual(list((root/'out').glob('.small_0-*')),[])

            # A successfully verified build publishes Rust first and the
            # attesting receipt last, preserving a content-addressed digest.
            def successful_build(command, **kwargs):
                self.assertFalse(receipt_path.exists())
                return subprocess.CompletedProcess(command, 0, stdout='', stderr='')

            with patch('verify_source_graph.subprocess.run', side_effect=successful_build):
                accepted=validate_and_generate(inp,golden,root/'out',root,True)
            published=json.loads(receipt_path.read_text())
            self.assertEqual(published,accepted)
            self.assertEqual(published['rust_acceptance_test_sha256'],
                             hashlib.sha256(rust_path.read_bytes()).hexdigest())
            self.assertTrue(receipt_path.read_bytes().endswith(b'\n'))
            graph['command']['opcode']='set:0:0'
            inp.write_text(json.dumps(graph)+'\n')
            with self.assertRaisesRegex(ValueError,'physical instruction mismatch'):
                validate_and_generate(inp,golden,root/'out',root,False)
            graph['command']['opcode']='set:0:1'
            inp.write_text(json.dumps(graph)+'\n')
            (golden/(ident+'.table')).write_bytes(raw.replace(b'set:0:1:0',b'set:0:0:0'))
            with self.assertRaisesRegex(ValueError,'hash mismatch'):
                validate_and_generate(inp,golden,root/'out',root,False)

if __name__=='__main__':unittest.main()
