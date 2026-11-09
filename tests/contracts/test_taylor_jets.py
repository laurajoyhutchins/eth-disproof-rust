from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
"""Independent exact tests for truncated Taylor recovery of the paper identity."""
import random
import unittest
from itertools import product
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.network import simple_network
from non_exponential_sudoku.core.jets import JetRing
from reference.local_support import pin_band_wires
from reference.real_sudoku_bench import REFERENCE_9, independent_count_sparse, puzzles
from non_exponential_sudoku.sudoku.three_cnf import Puzzle


def multi_swap_puzzle(rectangles=2):
    # These are different valid independently swappable rectangles in the
    # fixed 9x9 solution. The fixtures contain only givens, never a solution.
    groups=((3,4,30,31),(16,17,61,62),(22,23,49,50))
    x=list(map(int,REFERENCE_9))
    for cells in groups[:rectangles]:
        for cell in cells:x[cell]=0
    return Puzzle(3,tuple(x))


class TaylorJetTests(unittest.TestCase):
    def test_polynomial_modulus_and_exact_inverse(self):
        rng=random.Random(5743)
        for e,p,q in ((2,3,2),(4,9,5),(5,31,7)):
            B=Padic(e,modulus_polynomial(e),p);J=JetRing(B,q)
            for _ in range(15):
                a=tuple(tuple(rng.randrange(1<<p) for _ in range(e)) for k in range(q))
                if not any(x & 1 for x in a[0]):continue
                inverse=J.inv(a)
                self.assertEqual(J.mul(a,inverse),J.one)
                self.assertEqual(J.mul(a,J.variable)[:2],(B.zero,a[0]))
                self.assertEqual(J.add(a,J.neg(a)),J.zero)
    def test_truncation_homomorphism(self):
        B=Padic(4,modulus_polynomial(4),17)
        big=JetRing(B,7);small=JetRing(B,3)
        rng=random.Random(66)
        for _ in range(30):
            a=tuple(tuple(rng.randrange(1<<B.p) for _ in range(B.e)) for _ in range(7))
            b=tuple(tuple(rng.randrange(1<<B.p) for _ in range(B.e)) for _ in range(7))
            self.assertEqual(big.mul(a,b)[:3],small.mul(a[:3],b[:3]))
    def test_small_networks_both_recovery_routes(self):
        rng=random.Random(942)
        for n in (1,2,3):
            bits=list(product((0,1),repeat=n))
            for _ in range(4):
                l={x:rng.randrange(2) for x in bits}
                r={x:rng.randrange(2) for x in bits}
                net=simple_network(n,[ (tuple(range(n)),l) ],[ (tuple(range(n)),r) ])
                expected=sum(l[x]*r[x] for x in bits)
                labels=(((0,),),((1,),))
                results=[]
                for recovery in ('interpolate','jet'):
                    c=ContractionEngine(ContractorConfig(n, n+2, schedule='micro', recovery=RecoveryConfig(method=recovery), leaf=LeafConfig(strategy='eliminate'), root_labels=labels))
                    results.append(c.contract(net))
                self.assertEqual(results[0],results[1])
                self.assertEqual(results[0][0],expected)
    def test_sudoku_4_8_wires_and_independent_counts(self):
        for name,p,expected in puzzles():
            if name not in ('9x9-77-givens-two-solutions','9x9-73-givens-four-solutions'):
                continue
            net,_=pin_band_wires(p)
            out=[]
            for method in ('interpolate','jet'):
                c=ContractionEngine(ContractorConfig(net.edges, net.edges+1, schedule='micro', recovery=RecoveryConfig(method=method), leaf=LeafConfig(strategy='eliminate')))
                out.append(c.contract(net))
            self.assertEqual(out[0],out[1])
            self.assertEqual(out[0][0],expected)
    def test_12_wire_independent_reference(self):
        p=multi_swap_puzzle(2)
        self.assertEqual(independent_count_sparse(p,12),4)
        net,details=pin_band_wires(p)
        self.assertEqual(net.edges,12)
        c=ContractionEngine(ContractorConfig(net.edges, net.edges+1, schedule='micro', recovery=RecoveryConfig(method='jet'), leaf=LeafConfig(strategy='eliminate')))
        ans=c.contract(net)
        self.assertEqual(ans[0],4)
        self.assertTrue(all(x==0 for x in ans[1:]))
        self.assertEqual(c.stats.interpolation_evaluations,2)
        self.assertGreater(c.stats.mode_dp_local_child_evaluations,0)
        self.assertGreater(c.stats.leaves,0)
    def test_paper_jet_branch_not_asserted_verified(self):
        # The original proof uses residue-point interpolation at every
        # level. Nested jets are a derived experimental optimization.
        with self.assertRaises(ValueError):
            ContractionEngine(ContractorConfig(4, 5, schedule='paper', recovery=RecoveryConfig(method='jet')))



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.integration
