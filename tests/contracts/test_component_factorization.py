from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
"""Exact connected-child factorization and weighted-fill verification."""
import random
import unittest
from itertools import product

from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.elimination.engine import ModeEliminator
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.core.modes import Mode, mode_catalog, weighted_tuples
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.contraction.children import child_components, make_child
from non_exponential_sudoku.core.network import indicator_entry, simple_network, Network, Vertex
from non_exponential_sudoku.core.packing import pack
from tests.support.mode_factors import synthetic_modes, reference_factor_sum, dp_sum


class ComponentFactorization(unittest.TestCase):
    def crossing(self, count):
        net=simple_network(count,
            [([j], {(0,):1,(1,):1}) for j in range(count)],
            [([j], {(0,):1,(1,):1}) for j in range(count)])
        packing=pack(net,64,2,
             (tuple((0,0) for _ in range(count)),
              tuple((1,0) for _ in range(count))))
        return net,packing

    def test_child_component_product_matches_whole_for_modes(self):
        net,packing=self.crossing(4)
        contractor=ContractionEngine(ContractorConfig(4, 8, schedule='geometry64', leaf=LeafConfig(strategy='eliminate')))
        R=Padic(contractor.e,contractor.f,9)
        modes=mode_catalog(net,packing,1,R.p)
        rng=random.Random(2718)
        for g in (0,1):
            comps=child_components(net,packing,g,0)
            self.assertGreater(len(comps),1)
            for _ in range(9):
                beta=tuple(rng.randrange(min(len(m.rows),(R.p-1)//m.weight)+1) for m in modes)
                full=make_child(net,packing,modes,beta,1,R.basis(3),R,g,0)
                self.assertLessEqual(full.edges,16)
                expected=full.direct(R,16)
                got=R.one
                for component in comps:
                    members=set(component.packets)
                    selected=[j for j,m in enumerate(modes) if m.packet in members and
                              g in (m.source,m.target)]
                    child=make_child(net,packing,[modes[j] for j in selected],
                          tuple(beta[j] for j in selected),1,R.basis(3),R,g,0,
                          component=component)
                    got=R.mul(got,child.direct(R,16))
                self.assertEqual(got,expected)

    def test_zero_port_vertex_is_not_lost(self):
        def two(bits,R):return R.scalar(2)
        def one(bits,R):return R.one
        net=Network([Vertex('lonely',(),two),Vertex('L',(0,),one)],
                    [Vertex('R',(0,),one)],1)
        net.validate()
        packing=pack(net,64,2,(((0,0),(0,0)),((0,0),)))
        R=Padic(5,modulus_polynomial(5),5)
        components=child_components(net,packing,0,0)
        full=make_child(net,packing,[],(),1,R.basis(1),R,0,0)
        got=R.one
        for comp in components:
            child=make_child(net,packing,[],(),1,R.basis(1),R,0,0,component=comp)
            got=R.mul(got,child.direct(R))
        self.assertEqual(full.direct(R),got)
        self.assertEqual(got[0],4)

    def test_new_factorization_equals_old_real_contraction(self):
        for size,p in ((4,9),(8,12)):
            net,packing=self.crossing(size)
            results={}
            for factorization in ('whole','components'):
                c=ContractionEngine(ContractorConfig(size, p, schedule='geometry64', mode=ModeConfig(factorization=factorization, order='min_fill'), limits=ModeLimits(max_factor_states=100000, max_operations=10000000), leaf=LeafConfig(strategy='eliminate')))
                R=Padic(c.e,c.f,p)
                modes=mode_catalog(net,packing,1,p)
                result=c.evaluate_deformation(net,packing,modes,1,R.basis(3),R,0)
                self.assertEqual(result,R.scalar(1<<size))
                results[factorization]=result
            self.assertEqual(results['whole'],results['components'])

    def test_shared_parent_vertex_prevents_false_packet_split(self):
        # A single retained left vertex spanning several packets connects
        # them in the child topology. They may NOT be factored independently.
        def one(bits,R):return R.one
        net=Network([Vertex('shared-left',tuple(range(12)),one)],
                    [Vertex('right-'+str(j),(j,),one) for j in range(12)],12)
        net.validate()
        packing=pack(net,64,2,(((0,0),),tuple((1,0) for _ in range(12))))
        self.assertGreater(len(packing.packets),1)
        components=child_components(net,packing,0,0)
        self.assertEqual(len(components),1)
        self.assertEqual(len(components[0].packets),len(packing.packets))
        R=Padic(5,modulus_polynomial(5),6)
        modes=mode_catalog(net,packing,1,R.p)
        whole=make_child(net,packing,modes,(0,)*len(modes),1,R.basis(2),R,0,0)
        split=make_child(net,packing,modes,(0,)*len(modes),1,R.basis(2),R,0,0,
                         component=components[0])
        self.assertEqual(whole.edges,split.edges)
        self.assertEqual(whole.direct(R,16),split.direct(R,16))

    def test_component_path_survives_whole_factor_refusal(self):
        size=20;p=8
        net,packing=self.crossing(size)
        modes=mode_catalog(net,packing,1,p)
        self.assertGreater(len(modes),size)
        c=ContractionEngine(ContractorConfig(size, p, schedule='geometry64', mode=ModeConfig(factorization='whole')))
        R=Padic(c.e,c.f,p)
        # Sharpened valuations remove the previous artificial factor
        # explosion. The whole route now reaches an independent leaf
        # limit, while component factoring still completes exactly.
        with self.assertRaisesRegex(CapacityError,'Direct leaf has 20 edges'):
            c.evaluate_deformation(net,packing,modes,1,R.basis(3),R,0)
        c=ContractionEngine(ContractorConfig(size, p, schedule='geometry64', mode=ModeConfig(factorization='components')))
        self.assertEqual(c.evaluate_deformation(net,packing,modes,1,R.basis(3),R,0),R.scalar(1<<size))
        self.assertEqual(c.stats.mode_tuples,0)
        self.assertEqual(c.stats.mode_dp_components,len(packing.packets))
        self.assertLessEqual(c.stats.mode_dp_max_local_arity_after,8)

    def test_nested_coefficient_ring_component_equality(self):
        net,packing=self.crossing(2)
        c=ContractionEngine(ContractorConfig(2, 9, schedule='geometry64', leaf=LeafConfig(strategy='eliminate')))
        B=Padic(c.e,c.f,9)
        R=JetRing(B,3)
        z=R.variable
        modes=mode_catalog(net,packing,1,R.p)
        outputs=[]
        for split in ('whole','components'):
            calc=ContractionEngine(ContractorConfig(2, 9, schedule='geometry64', mode=ModeConfig(factorization=split), recovery=RecoveryConfig(method='jet'), leaf=LeafConfig(strategy='eliminate')))
            outputs.append(calc.evaluate_deformation(net,packing,modes,1,z,R,0))
        self.assertEqual(outputs[0],outputs[1])

    def test_component_budget_enforced_without_enumeration(self):
        net,packing=self.crossing(8)
        c=ContractionEngine(ContractorConfig(8, 12, schedule='geometry64', limits=ModeLimits(max_components=1)))
        R=Padic(c.e,c.f,12)
        modes=mode_catalog(net,packing,1,12)
        with self.assertRaisesRegex(CapacityError,'component-count limit'):
            c.evaluate_deformation(net,packing,modes,1,R.basis(1),R,0)
        self.assertEqual(c.stats.mode_tuples,0)


class ScopedElimination(unittest.TestCase):
    def test_budget_admissible_factor_states_not_raw_product(self):
        B=Padic(5,modulus_polynomial(5),3)
        modes=synthetic_modes([(0,1)]*12,B.p)
        def fn(group,scope,beta):return B.scalar(1)
        # Raw domain product is 2^12=4096, but weight<3 admits
        # 1+12+66=79 tuples; the exact budget-pruned local table fits.
        result,stats=dp_sum(modes,B,fn,max_factor_states=100,
                   max_operations=30000,max_child_contractions=500)
        self.assertEqual(result,B.scalar(79))
        self.assertEqual(stats.mode_dp_local_child_evaluations,158)

    def test_orderings_agree_on_mixed_sparse_graphs(self):
        rng=random.Random(421)
        B=Padic(5,modulus_polynomial(5),5)
        for _ in range(12):
            edges=[tuple(rng.sample(range(6),2)) for j in range(6)]
            modes=synthetic_modes(edges,B.p)
            scopes={g:tuple(j for j,m in enumerate(modes) if g in (m.source,m.target))
                    for pair in edges for g in pair}
            tables={g:{bits:B.scalar(rng.randrange(7)) for bits in product((0,1),repeat=len(scope))}
                    for g,scope in scopes.items()}
            def fn(g,scope,bits):return tables[g][bits]
            expected=reference_factor_sum(modes,B,fn)
            for order in ('min_states','min_fill'):
                got,stats=dp_sum(modes,B,fn,order=order)
                self.assertEqual(got,expected)
                self.assertLessEqual(stats.mode_dp_eliminations,len(modes))

    def test_min_fill_reduces_actual_intermediate_width(self):
        # Connected six-group graph with repeated pair interactions. This is
        # a reproducible instance where the minimum immediate table-size
        # heuristic makes extra fill edges, while min-fill avoids them.
        edges=[(2,4),(2,3),(4,2),(1,2),(2,0),(4,2),(0,3),
               (2,1),(3,1),(3,5),(0,1),(1,5),(0,3),(1,5)]
        R=Padic(5,modulus_polynomial(5),4)
        modes=synthetic_modes(edges,R.p)
        def fn(g,scope,assignment):
            return R.scalar(g+1+sum((j+1)*(b+1) for j,b in zip(scope,assignment)))
        expected=reference_factor_sum(modes,R,fn)
        old,old_stats=dp_sum(modes,R,fn,order='min_states')
        new,new_stats=dp_sum(modes,R,fn,order='min_fill')
        self.assertEqual(expected,old)
        self.assertEqual(expected,new)
        self.assertEqual(old_stats.mode_dp_max_scope,8)
        self.assertEqual(new_stats.mode_dp_max_scope,6)
        self.assertLess(new_stats.mode_dp_operations,old_stats.mode_dp_operations)

    def test_invalid_scope_partition_fails_closed(self):
        B=Padic(5,modulus_polynomial(5),4)
        modes=synthetic_modes([(0,1)],B.p)
        class Stats:
            mode_dp_variables=0;mode_dp_groups=0
        with self.assertRaisesRegex(ValueError,'partition'):
            ModeEliminator(modes,{0,1},B,lambda *a:B.one,Stats(),CapacityError,
                factor_scopes={(0,0):(),(1,0):(0,)})




# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.extended
