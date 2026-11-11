"""Synthetic structural regression only, never original-source acceptance."""
import json
import unittest
from compute_l_structural_acceptance import structural_summary, TARGET
from verify_source_graph import SOURCE_SHA


class ComputeLShapeContracts(unittest.TestCase):
    def test_bounded_recursive_composition_has_exact_source_label_count(self):
        def callee(labels):
            return {'kind':'call','program':{
                'r':3,'s':3,'labels':labels,'input':0,'output':0,'entry':0,
                'code':['goto:0']*(labels-1)+['halt']}}
        cmd={'kind':'skip'}
        for _ in range(16):
            cmd={'kind':'seq','first':cmd,'second':callee(11)}
        cmd={'kind':'seq','first':cmd,'second':{
            'kind':'seq','first':callee(24),'second':callee(11)}}
        blob='1'*40
        rec={'fqn':TARGET,'git_blob':blob,'id':'synthetic_shape'}
        graph={'kind':'original-structured-source-v1','source_commit':SOURCE_SHA,
               'source_blob':blob,'declaration':TARGET,'id':rec['id'],
               'abi':{'r':3,'s':3,'labels':212,'input':0,'output':0},
               'command':cmd}
        result,root=structural_summary(json.dumps(graph)+'\n',rec)
        self.assertEqual(result['labels'],212)
        self.assertEqual(result['calls'],{11:17,24:1})
        self.assertEqual(result['node_count'],37)
        self.assertEqual(root.size+1,212)
        graph['abi']['labels']=211
        with self.assertRaises(ValueError):
            structural_summary(json.dumps(graph)+'\n',rec)
        graph['abi']['labels']=212
        graph['command']['second']['second']['program']['code']=['halt']
        with self.assertRaises(ValueError):
            structural_summary(json.dumps(graph)+'\n',rec)

if __name__=='__main__': unittest.main()