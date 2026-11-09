"""Reference-versus-DP verification of the exact weighted mode identity."""
from __future__ import annotations
from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig

import random
import unittest
from itertools import product

from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.elimination.engine import ModeEliminator
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.core.modes import Mode, mode_catalog, weighted_tuples
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.sudoku.encoding import independently_evaluate_F
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.core.network import simple_network
from reference.real_sudoku_bench import puzzles, independent_count_sparse
from reference.local_support import pin_band_wires
from reference.scaling_experiment import parity_network, independent_count


from tests.support.mode_factors import synthetic_modes, reference_factor_sum, dp_sum, ModeStats as Stats

class ModeDPAlgebra(unittest.TestCase):
    def setUp(self):
        self.B=Padic(5,modulus_polynomial(5),7)

    def test_connected_cycle_exact(self):
        rng=random.Random(719)
        for pairs in (
            [(0,1),(1,2),(2,3)],
            [(0,1),(1,2),(2,3),(3,0)],
            [(0,1),(0,1),(1,2),(2,0)],
            [(0,1),(2,3),(4,5),(6,7)],
        ):
            modes=synthetic_modes(pairs,self.B.p)
            group_scopes={g:tuple(j for j,m in enumerate(modes)
                             if g in (m.source,m.target))
                          for pair in pairs for g in pair}
            random_factors={g:{assignment:self.B.scalar(rng.randrange(0,13))
                          for assignment in product((0,1),repeat=len(scope))}
                          for g,scope in group_scopes.items()}
            def fn(g,scope,assignment):
                self.assertEqual(scope,group_scopes[g])
                return random_factors[g][assignment]
            expected=reference_factor_sum(modes,self.B,fn)
            got,stats=dp_sum(modes,self.B,fn)
            self.assertEqual(got,expected)
            self.assertEqual(stats.mode_dp_eliminations,len(modes))

    def test_weight_truncation_and_higher_multiplicity(self):
        R=Padic(5,modulus_polynomial(5),3)
        modes=[Mode(j,0,b,source,target,b+1,(),rows)
                for j,(source,target,b,rows) in enumerate([
                (0,1,0,(0,1)),(1,2,1,(0,1)),(2,3,0,(0,1))])]
        def fn(g,scope,assignment):
            return R.scalar(1+g+sum((j+1)*b for j,b in zip(scope,assignment)))
        expected=reference_factor_sum(modes,R,fn)
        got,_=dp_sum(modes,R,fn)
        self.assertEqual(expected,got)

    def test_nested_jet_ring_and_precisions(self):
        for p in (3,7):
            B=Padic(5,modulus_polynomial(5),p)
            for R in (JetRing(B,3),JetRing(JetRing(B,2),2)):
                modes=synthetic_modes([(0,1),(1,2),(2,0)],p)
                def fn(g,scope,assignment):
                    v=R.add(R.scalar(g+1),R.variable)
                    for j,b in zip(scope,assignment):
                        if b:v=R.mul(v,R.add(R.scalar(j+1),R.variable))
                    return v
                self.assertEqual(dp_sum(modes,R,fn)[0],
                                 reference_factor_sum(modes,R,fn))

    def test_no_modes_and_zero_factor(self):
        R=self.B
        def one(g,scope,assignment):return R.scalar(g+2)
        got,_=dp_sum([],R,one)
        self.assertEqual(got,R.one)
        stats=Stats()
        got=ModeEliminator([], {1,2,4},R,one,stats,CapacityError).run()
        self.assertEqual(got,R.scalar(3*4*6))
        modes=synthetic_modes([(0,1)],R.p)
        def zero(g,scope,assignment):return R.zero if g==1 else R.one
        self.assertEqual(dp_sum(modes,R,zero)[0],R.zero)

    def test_refuses_factor_state_memory_and_work_blowup(self):
        modes=synthetic_modes([(0,1),(0,2),(0,3)],self.B.p)
        fn=lambda *args:self.B.one
        for opts in ({'max_factor_states':3},
                     {'max_live_terms':2},
                     {'max_operations':1},
                     {'max_child_contractions':2},
                     {'max_estimated_bytes':200}):
            with self.subTest(opts=opts):
                with self.assertRaises(CapacityError):dp_sum(modes,self.B,fn,**opts)


class ActualContractions(unittest.TestCase):
    def test_actual_four_slot_crossing_networks(self):
        for count in (1,2,4):
            net=simple_network(count,
                [([i],{(0,):1,(1,):1}) for i in range(count)],
                [([i],{(0,):1,(1,):1}) for i in range(count)])
            labels=(tuple((2*i,0) for i in range(count)),
                    tuple((2*i+1,0) for i in range(count)))
            packing=pack(net,64,2,labels)
            for t in (-1,1):
                a=ContractionEngine(ContractorConfig(count, 12, schedule='geometry64', mode=ModeConfig(strategy='enumerate'), leaf=LeafConfig(strategy='eliminate')))
                b=ContractionEngine(ContractorConfig(count, 12, schedule='geometry64', mode=ModeConfig(strategy='eliminate'), leaf=LeafConfig(strategy='eliminate')))
                R=Padic(a.e,a.f,12)
                modes=mode_catalog(net,packing,t,R.p)
                for z in (R.zero,R.basis(3)):
                    v=a.evaluate_deformation(net,packing,modes,t,z,R,0)
                    w=b.evaluate_deformation(net,packing,modes,t,z,R,0)
                    self.assertEqual(v,w)
                    self.assertEqual(v,independently_evaluate_F(net,packing,t,z,R))

    def test_sudoku_and_connected_parity_full_recursion(self):
        cases=[]
        for family,span in (('cycle2',1),('cycle2',2),('ladder3',2)):
            net=parity_network(family,span)
            cases.append((family+str(span),net,independent_count(family,span)[0]))
        for name,p,expected in puzzles():
            if name in ('9x9-77-givens-two-solutions','9x9-73-givens-four-solutions'):
                self.assertEqual(independent_count_sparse(p),expected)
                cases.append((name,pin_band_wires(p)[0],expected))
        for name,net,expected in cases:
            for strategy in ('enumerate','eliminate'):
                with self.subTest(name=name,strategy=strategy):
                    calc=ContractionEngine(ContractorConfig(net.edges, net.edges+3, schedule='micro', mode=ModeConfig(strategy=strategy), recovery=RecoveryConfig(method='jet', streaming=True), leaf=LeafConfig(strategy='eliminate')))
                    value=calc.contract(net)
                    self.assertEqual(value[0],expected)
                    self.assertTrue(all(v==0 for v in value[1:]))
                    if strategy=='eliminate':
                        self.assertEqual(calc.stats.mode_tuples,0)

    def test_actual_capacity_refusal_does_not_fallback(self):
        name,puzzle,expected=next((n,p,c) for n,p,c in puzzles()
            if n=='9x9-73-givens-four-solutions')
        net,_=pin_band_wires(puzzle)
        dp=ContractionEngine(ContractorConfig(net.edges, net.edges+3, schedule='micro', mode=ModeConfig(strategy='eliminate'), limits=ModeLimits(max_factor_states=8), recovery=RecoveryConfig(method='jet'), leaf=LeafConfig(strategy='eliminate')))
        with self.assertRaisesRegex(CapacityError,'factor size limit'):
            dp.contract(net)
        # If the local state limit is raised, the SAME mathematical
        # contraction completes, without switching to tuple enumeration.
        dp_ok=ContractionEngine(ContractorConfig(net.edges, net.edges+3, schedule='micro', mode=ModeConfig(strategy='eliminate'), limits=ModeLimits(max_factor_states=512), recovery=RecoveryConfig(method='jet'), leaf=LeafConfig(strategy='eliminate')))
        self.assertEqual(dp_ok.contract(net)[0],expected)
        self.assertEqual(dp_ok.stats.mode_tuples,0)

    def test_reference_tuple_cap_is_not_applied_to_dp(self):
        count=8
        net=simple_network(count,
             [([i],{(0,):1,(1,):1}) for i in range(count)],
             [([i],{(0,):1,(1,):1}) for i in range(count)])
        labels=(tuple((2*i,0) for i in range(count)),
                tuple((2*i+1,0) for i in range(count)))
        packing=pack(net,64,2,labels)
        for strategy in ('enumerate','eliminate'):
            calc=ContractionEngine(ContractorConfig(count, 8, schedule='geometry64', mode=ModeConfig(strategy=strategy, max_tuples=8), leaf=LeafConfig(strategy='eliminate')))
            R=Padic(calc.e,calc.f,14)
            modes=mode_catalog(net,packing,1,R.p)
            if strategy=='enumerate':
                with self.assertRaisesRegex(CapacityError,'Mode tuple resource limit'):
                    calc.evaluate_deformation(net,packing,modes,1,R.basis(3),R,0)
            else:
                self.assertEqual(calc.evaluate_deformation(net,packing,modes,1,R.basis(3),R,0),
                                 R.scalar(1<<count))
                self.assertEqual(calc.stats.mode_tuples,0)

    def test_actual_dense_mode_graph_refuses_preallocation(self):
        count=20
        net=simple_network(count,
             [([i],{(0,):1,(1,):1}) for i in range(count)],
             [([i],{(0,):1,(1,):1}) for i in range(count)])
        labels=(tuple((0,0) for _ in range(count)),
                tuple((1,0) for _ in range(count)))
        packing=pack(net,64,2,labels)
        calc=ContractionEngine(ContractorConfig(count, 8, schedule='geometry64', mode=ModeConfig(strategy='eliminate', factorization='whole'), limits=ModeLimits(max_factor_states=4096)))
        R=Padic(calc.e,calc.f,8)
        modes=mode_catalog(net,packing,1,R.p)
        self.assertGreater(len(modes),20)
        with self.assertRaisesRegex(CapacityError,'factor size limit'):
            calc.evaluate_deformation(net,packing,modes,1,R.basis(3),R,0)
        self.assertEqual(calc.stats.mode_dp_local_child_evaluations,0)

    def test_multilevel_nested_recursion(self):
        net=parity_network('cycle2',1)
        expected=independent_count('cycle2',1)[0]
        for strategy in ('enumerate','eliminate'):
            calc=ContractionEngine(ContractorConfig(net.edges, net.edges+3, schedule='micro', mode=ModeConfig(strategy=strategy), recovery=RecoveryConfig(method='jet', streaming=True), leaf=LeafConfig(strategy='eliminate'), micro_active_depth=2))
            self.assertEqual(calc.contract(net)[0],expected)



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.integration
