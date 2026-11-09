from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
"""Differential verification of precision-aware lazy *real* packet entries."""
import itertools
import unittest
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.sudoku.encoding import port_graph_with_cross_mode
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.contraction.children import make_child
from non_exponential_sudoku.contraction.packets import EvaluationContext
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.packet_lazy import LazyPacketJet, PacketCoefficientCapacityError
from reference.scaling_experiment import parity_network, independent_count


class PacketOracleTests(unittest.TestCase):
    def test_real_nonzero_mode_packet_entry_at_multiple_precisions(self):
        net=port_graph_with_cross_mode()
        packing=pack(net,2,1,(((0,),),((1,),)))
        for p in (9,15):
            B=Padic(5,modulus_polynomial(5),p)
            for outer in (B,JetRing(B,2)):
                R=JetRing(outer,3)
                for t in (-1,1):
                    modes=mode_catalog(net,packing,t,p)
                    betas=[(0,)] if modes else [()]
                    if modes:betas.append((1,))
                    for beta in betas:
                        dense_ctx=EvaluationContext(t,R.variable,R,1)
                        lazy_ctx=EvaluationContext(t,R.variable,R,1,
                            packet_coeff_cache_limit=128)
                        for g in (0,1):
                            d=make_child(net,packing,modes,beta,t,R.variable,R,g,0,dense_ctx)
                            l=make_child(net,packing,modes,beta,t,R.variable,R,g,0,lazy_ctx)
                            self.assertEqual(d.edges,l.edges)
                            for dv,lv in zip(d.right,l.right):
                                self.assertEqual(dv.ports,lv.ports)
                                for bits in itertools.product((0,1),repeat=len(dv.ports)):
                                    self.assertEqual(dv.oracle(bits,R),lv.oracle(bits,R),
                                        (p,t,beta,g,bits))
                        self.assertLessEqual(lazy_ctx.R.oracle.max_cached,128)
                        self.assertGreater(lazy_ctx.R.materializations,0)

    def test_coefficients_at_nontrivial_parent_jet_and_lift(self):
        net=port_graph_with_cross_mode();packing=pack(net,2,1,(((0,),),((1,),)))
        B=Padic(5,modulus_polynomial(5),17)
        outer=JetRing(B,3)
        R=JetRing(outer,3)
        for t in (-1,1):
            modes=mode_catalog(net,packing,t,R.p)
            beta=(1,) if modes else ()
            dense=EvaluationContext(t,R.variable,R,1)
            lazy=EvaluationContext(t,R.variable,R,1,packet_coeff_cache_limit=256)
            d=make_child(net,packing,modes,beta,t,R.variable,R,0,0,dense)
            l=make_child(net,packing,modes,beta,t,R.variable,R,0,0,lazy)
            lifted=JetRing(R,2)
            for dv,lv in zip(d.right,l.right):
                for bits in itertools.product((0,1),repeat=len(dv.ports)):
                    self.assertEqual(dv.oracle(bits,R),lv.oracle(bits,R))
                    self.assertEqual(dv.oracle(bits,lifted),lv.oracle(bits,lifted))

    def test_checkpointed_packet_coefficients_match_dense_at_multiple_precisions(self):
        net=port_graph_with_cross_mode()
        packing=pack(net,2,1,(((0,),),((1,),)))
        for p in (11, 21):
            B=Padic(5,modulus_polynomial(5),p)
            R=JetRing(B,4)
            for t in (-1,1):
                modes=mode_catalog(net,packing,t,R.p)
                dense=EvaluationContext(t,R.variable,R,1)
                for budget in (0,20,1000):
                    sparse=EvaluationContext(t,R.variable,R,1,
                        packet_coeff_cache_limit=128,
                        packet_checkpoint_coordinates=budget)
                    self.assertLessEqual(sparse.R.checkpoint_used,budget)
                    beta=(1,) if modes else ()
                    for group in (0,1):
                        original=make_child(net,packing,modes,beta,t,R.variable,R,group,0,dense)
                        changed=make_child(net,packing,modes,beta,t,R.variable,R,group,0,sparse)
                        for left,right in zip(original.right,changed.right):
                            for bits in itertools.product((0,1),repeat=len(left.ports)):
                                self.assertEqual(left.oracle(bits,R),right.oracle(bits,R))
                    self.assertLessEqual(sparse.R.checkpoint_used,budget)

    def test_expression_dag_refusal_is_explicit(self):
        R=JetRing(Padic(5,modulus_polynomial(5),9),4)
        with self.assertRaises(PacketCoefficientCapacityError):
            LazyPacketJet(R,8,node_limit=2)

    def test_budget_refusal_instead_of_incorrect_fallback(self):
        R=JetRing(Padic(5,modulus_polynomial(5),15),7)
        lazy=LazyPacketJet(R,0,miss_limit=20)
        poly=lazy.add(lazy.one,lazy.variable)
        for _ in range(6):poly=lazy.mul(poly,poly)
        with self.assertRaises(PacketCoefficientCapacityError):lazy.materialize(poly)

    def test_nonzero_mode_end_to_end_same_count_and_call_trace(self):
        net=port_graph_with_cross_mode()
        rows=[]
        for cache in (None,0,32,256):
            c=ContractionEngine(ContractorConfig(1, 4, schedule='micro', recovery=RecoveryConfig(method='jet', streaming=True), packets=PacketConfig(cache_limit=cache), leaf=LeafConfig(strategy='eliminate'), root_labels=(((0,),),((1,),))))
            result=c.contract(net)
            rows.append((result,c.stats.mode_tuples,c.stats.recursive_calls))
        self.assertEqual(rows,[rows[0]]*len(rows))
        self.assertEqual(rows[0][0][0],1)

    def test_nested_two_level_parity_count(self):
        net=parity_network('cycle2',1)
        expected,_=independent_count('cycle2',1)
        outputs=[]
        for cache in (None,256):
            c=ContractionEngine(ContractorConfig(net.edges, net.edges+3, schedule='micro', recovery=RecoveryConfig(method='jet', streaming=True), packets=PacketConfig(cache_limit=cache), leaf=LeafConfig(strategy='eliminate'), micro_active_depth=2))
            outputs.append(c.contract(net))
        self.assertEqual(outputs[0],outputs[1])
        self.assertEqual(outputs[0][0],expected)



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.integration
