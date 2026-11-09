from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
import unittest
import random
from itertools import product
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial, poly_remainder, poly_square
from non_exponential_sudoku.core.packing import pack, audit_packing
from non_exponential_sudoku.core.modes import mode_catalog, weighted_tuples
from non_exponential_sudoku.core.network import simple_network
from non_exponential_sudoku.sudoku.encoding import sudoku_network
from reference.sudoku_network_oracle import independently_evaluate_F
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.contraction.packets import cauchy_values, cross_mode_coefficient
from non_exponential_sudoku.sudoku.three_cnf import Puzzle

class ExtensionRingTests(unittest.TestCase):
    def test_inverse_and_ring_axioms(self):
        R=Padic(5,modulus_polynomial(5),11)
        elems=[R.basis(k) for k in range(1,15)]
        for a,b,c in zip(elems,elems[1:],elems[2:]):
            self.assertEqual(R.mul(a,R.add(b,c)),R.add(R.mul(a,b),R.mul(a,c)))
            self.assertEqual(R.mul(a,R.inv(a)),R.one)
            self.assertEqual(R.mul(a,b),R.mul(b,a))
    def test_cauchy_matches_paper_rationals_mod_power_two(self):
        from reference.paper_algebra import cauchy_kernel, eval_poly
        from fractions import Fraction
        R=Padic(5,modulus_polynomial(5),20)
        for L in (2,4):
            for t in range(-L,L):
                for z in (R.zero,R.one,R.basis(3)):
                    vals=cauchy_values(t,z,R,L)
                    for delta in range(-(L-1),L):
                        if z in (R.zero,R.one):
                            value=eval_poly(cauchy_kernel(L,0,delta),t+2*L*z[0]) if delta>=0 else eval_poly(cauchy_kernel(L,-delta,0),t+2*L*z[0])
                            self.assertEqual(vals[delta],R.rational(value))
    def test_mode_expansion_nonzero_b(self):
        R=Padic(6,modulus_polynomial(6),14)
        L=4; t=1; z=R.basis(3)
        # For i=0, y0=0 and y=2, with x=0, cross-group.
        actual=cauchy_values(t,z,R,L)[2]
        approx=R.zero
        for b in range(R.p-1):
            coef=cross_mode_coefficient(t,z,R,L,0,0,b)
            approx=R.add(approx,coef) # j=1, so j^b=1
        self.assertEqual(actual,approx)

class RecursiveIdentityTests(unittest.TestCase):
    def setUp(self):
        self.labels=(((0,),),((1,),))
    def test_crossing_mode_is_used(self):
        net=simple_network(1,[([0],{(1,):1})],[([0],{(1,):1})])
        pk=pack(net,2,1,self.labels)
        modes=mode_catalog(net,pk,1,18)
        self.assertEqual(len(modes),1)
        # Normalized Cauchy cross coefficient carries 2^(a+1-i)=2^2.
        self.assertEqual(modes[0].weight,2)
        self.assertEqual(sorted(set(beta[0] for beta in weighted_tuples(modes,18))),[0,1])
        c=ContractionEngine(ContractorConfig(1, 4, schedule='micro', root_labels=self.labels))
        self.assertEqual(c.contract(net)[0],1)
        self.assertGreater(c.stats.child_networks,0)
        self.assertGreater(c.stats.mode_dp_local_child_evaluations,c.stats.interpolation_evaluations)
    def test_deformed_value_equals_crossing_recursion(self):
        net=simple_network(1,[([0],{(1,):1})],[([0],{(1,):1})])
        pk=pack(net,2,1,self.labels)
        c=ContractionEngine(ContractorConfig(1, 5, schedule='micro', root_labels=self.labels))
        for t in (-1,1):
            R=Padic(c.e,c.f,12)
            modes=mode_catalog(net,pk,t,R.p)
            for z in (R.one,R.basis(2)):
                expected=independently_evaluate_F(net,pk,t,z,R)
                actual=c.evaluate_deformation(net,pk,modes,t,z,R,0)
                self.assertEqual(actual,expected)
    def test_genuine_tiled_higher_modes_and_two_edges(self):
        # a=2, L=4. Two real edges occupy slots 0 and 2 in the SAME
        # packet, so the j=1 column forces genuine b>=1 tile modes.
        tab={(a,b):1 for a,b in product((0,1),repeat=2)}
        net=simple_network(2,[([0,1],tab)],[([0,1],tab)])
        labels=(((0,0),),((1,0),))
        pk=pack(net,2,2,labels)
        selected=[p for p in pk.packets if p.slots.count(0)==1]
        self.assertTrue(selected)
        self.assertEqual([i for i,e in enumerate(selected[0].slots) if e is not None],[0,2])
        c=ContractionEngine(ContractorConfig(2, 3, schedule='micro'))
        R=Padic(c.e,c.f,7)
        for t in (-1,1):
            modes=mode_catalog(net,pk,t,R.p)
            self.assertTrue(any(m.b>=1 for m in modes))
            for z in (R.one,R.basis(5)):
                expected=independently_evaluate_F(net,pk,t,z,R)
                actual=c.evaluate_deformation(net,pk,modes,t,z,R,0)
                self.assertEqual(actual,expected)

    def test_counts_multiple_small_truth_tables(self):
        for ls,rs,expected in [
            ({(0,):1,(1,):1},{(0,):1,(1,):1},2),
            ({(1,):1},{(0,):1},0),
            ({(0,):1},{(0,):1},1),
            ({(0,):1,(1,):1},{(1,):1},1),
        ]:
            with self.subTest(ls=ls,rs=rs):
                net=simple_network(1,[([0],ls)],[([0],rs)])
                c=ContractionEngine(ContractorConfig(1, 3, schedule='micro', root_labels=self.labels))
                self.assertEqual(c.contract(net)[0],expected)
    def test_sudoku_1x1_strict_and_micro(self):
        net=sudoku_network(Puzzle.from_text('.',1))
        c=ContractionEngine(ContractorConfig(net.edges, 2, schedule='paper'))
        self.assertEqual(c.contract(net)[0],1)
        self.assertEqual(c.stats.leaves,1)
        # Real recursive identity with forced nontrivial cross-group labels.
        c=ContractionEngine(ContractorConfig(net.edges, 2, schedule='micro', root_labels=(((0,),),((1,), (1,), (1,)))))
        self.assertEqual(c.contract(net)[0],1)
        self.assertGreater(c.stats.mode_dp_local_child_evaluations,0)
    def test_independent_two_edge_random_network_counts(self):
        rng=random.Random(4729)
        bits=list(product((0,1),repeat=2))
        for _ in range(16):
            left={b:rng.randrange(2) for b in bits}
            right={b:rng.randrange(2) for b in bits}
            expected=sum(left[b]*right[b] for b in bits)
            net=simple_network(2,[([0,1],left)],[([0,1],right)])
            forced=(((0,),),((1,),))
            audit=audit_packing(net,pack(net,2,1,forced))
            self.assertTrue(audit['all_edges_packed_exactly_once'])
            self.assertTrue(audit['orientation_geometry_valid'])
            c=ContractionEngine(ContractorConfig(2, 4, schedule='micro', root_labels=forced))
            self.assertEqual(c.contract(net)[0],expected)

    def test_random_three_edge_recursive_counts(self):
        rng=random.Random(1729)
        bits=list(product((0,1),repeat=3))
        for _ in range(5):
            left={b:rng.randrange(2) for b in bits}
            right={b:rng.randrange(2) for b in bits}
            expected=sum(left[b]*right[b] for b in bits)
            net=simple_network(3,[([0,1,2],left)],[([0,1,2],right)])
            c=ContractionEngine(ContractorConfig(3, 4, schedule='micro', root_labels=(((0,),),((1,),))))
            self.assertEqual(c.contract(net)[0],expected)
            self.assertGreater(c.stats.mode_dp_local_child_evaluations,0)

    def test_two_full_recursive_levels_and_canonical_lifts(self):
        # Unlike a one-layer demo, this visits depth 0 -> 1 -> 2, where
        # packet tensors from the first level are canonically lifted and
        # used as the second level's input tensor entries.
        tab={(a,b):1 for a,b in product((0,1),repeat=2)}
        net=simple_network(2,[([0,1],tab)],[([0,1],tab)])
        c=ContractionEngine(ContractorConfig(2, 3, schedule='micro', root_labels=(((0,),),((1,),)), micro_active_depth=2))
        self.assertEqual(c.contract(net)[0],4)
        self.assertGreater(c.stats.depth_counts.get(2,0),0)
        self.assertGreater(c.stats.depth_counts.get(1,0),0)

    def test_nine_by_nine_does_not_mislabel_exhaustive_search(self):
        net=sudoku_network(Puzzle.from_text('.'*81,3))
        c=ContractionEngine(ContractorConfig(net.edges, 325, schedule='paper'))
        with self.assertRaises(CapacityError):c.contract(net)



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.integration
