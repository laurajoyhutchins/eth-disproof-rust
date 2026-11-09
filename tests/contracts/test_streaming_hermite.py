from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
"""Exact, independent differential tests for streamed tapered recovery."""
import random
import unittest
from itertools import product

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.recovery.hermite import tapered_recover_over_ring
from non_exponential_sudoku.core.network import simple_network
from non_exponential_sudoku.core.jets import JetRing, precision_ring, embed_element
from non_exponential_sudoku.recovery.streaming import StreamingHermite
from reference.scaling_experiment import parity_network, independent_count
from reference.real_sudoku_bench import puzzles, independent_count_sparse
from reference.local_support import pin_band_wires

class StreamingRecoveryTests(unittest.TestCase):
    def test_center_by_center_agrees_with_original_for_random_jets(self):
        rng = random.Random(40239)
        for M,L,u in ((1,2,1),(2,4,1),(2,2,2)):
            base = Padic(5, modulus_polynomial(5), 7)
            for outer in (base, JetRing(base,2)):
                acc = StreamingHermite(M,L,u,outer)
                # Construct actual tapered jets from a low-degree polynomial F.
                # Arbitrary unrelated jets need not satisfy the global
                # divisibility condition of the exact Hermite formula.
                degree=min(3,M*(2*L-1))
                poly=[outer.scalar(rng.randrange(4)) for _ in range(degree+1)]
                if isinstance(outer, JetRing):
                    poly[0]=outer.add(poly[0],outer.variable)
                jets={}
                from math import comb
                for t,q in acc.qs.items():
                    if not q:continue
                    Rp=precision_ring(outer,acc.precision(t))
                    elevated=[embed_element(v,outer,Rp) for v in poly]
                    jets[t]=[]
                    for k in range(q):
                        v=Rp.zero
                        for j in range(k,len(poly)):
                            scale=comb(j,k)*(acc.alpha**k)*(t**(j-k))
                            v=Rp.add(v,Rp.mul(elevated[j],Rp.scalar(scale)))
                        jets[t].append(v)
                expected = tapered_recover_over_ring(jets,M,L,u,outer)
                for t in sorted(jets,reverse=True):acc.add_center(t,jets[t])
                self.assertEqual(acc.finish(),expected)
                self.assertEqual(expected,poly[0])
                self.assertEqual(acc.centers,len(jets))
                self.assertEqual(acc.max_center_coefficients,max(map(len,jets.values())))

    def test_rejects_missing_duplicate_and_bad_center(self):
        R = Padic(5,modulus_polynomial(5),11)
        acc = StreamingHermite(1,2,1,R)
        with self.assertRaises(ValueError):acc.finish()
        with self.assertRaises(ValueError):acc.add_center(0,[])
        t = -1; q=acc.qs[t]
        with self.assertRaises(ValueError):acc.add_center(t,[])
        Rp = precision_ring(R,acc.precision(t))
        acc.add_center(t,[Rp.zero]*q)
        with self.assertRaises(ValueError):acc.add_center(t,[Rp.zero]*q)
        for t in acc.qs:
            if t != -1 and acc.qs[t]:
                Rp=precision_ring(R,acc.precision(t))
                acc.add_center(t,[Rp.zero]*acc.qs[t])
        self.assertEqual(acc.finish(),R.zero)

    def test_random_truth_tables_nonzero_modes_micro(self):
        rng=random.Random(34)
        for M in (1,2,3):
            for _ in range(3):
                truth=list(product((0,1),repeat=M))
                left={x:rng.randrange(2) for x in truth}
                right={x:rng.randrange(2) for x in truth}
                expected=sum(left[x]*right[x] for x in truth)
                net=simple_network(M,[(tuple(range(M)),left)],[(tuple(range(M)),right)])
                results=[]
                for streaming in (False,True):
                    c=ContractionEngine(ContractorConfig(M, M+4, schedule='micro', recovery=RecoveryConfig(method='jet', streaming=streaming), leaf=LeafConfig(strategy='eliminate')))
                    v=c.contract(net)
                    self.assertEqual(v[0],expected)
                    results.append((v,c))
                self.assertEqual(results[0][0],results[1][0])
                self.assertGreater(results[1][1].stats.streaming_hermite_centers,0)
                self.assertLessEqual(results[1][1].stats.retained_jet_coefficients_peak,
                                     results[0][1].stats.retained_jet_coefficients_peak)

    def test_real_generalized_sudoku_exact_count(self):
        name,p,expected=next((n,p,c) for n,p,c in puzzles()
                             if n=='9x9-77-givens-two-solutions')
        self.assertEqual(independent_count_sparse(p,10),expected)
        net,_=pin_band_wires(p)
        outputs=[]
        for streaming in (False,True):
            c=ContractionEngine(ContractorConfig(net.edges, net.edges+2, schedule='micro', recovery=RecoveryConfig(method='jet', streaming=streaming), leaf=LeafConfig(strategy='eliminate')))
            outputs.append(c.contract(net))
        self.assertEqual(outputs[0],outputs[1])
        self.assertEqual(outputs[0][0],expected)

    def test_two_active_recursion_levels_match_eager_and_reference(self):
        net=parity_network('cycle2',1)
        expected,_=independent_count('cycle2',1)
        values=[]
        for streaming in (False,True):
            c=ContractionEngine(ContractorConfig(net.edges, net.edges+4, schedule='micro', recovery=RecoveryConfig(method='jet', streaming=streaming), leaf=LeafConfig(strategy='eliminate'), micro_active_depth=2))
            values.append(c.contract(net))
            self.assertGreater(c.stats.active_depth_counts.get(1,0),0)
        self.assertEqual(values[0],values[1])
        self.assertEqual(values[0][0],expected)

    def test_64_groups_preserves_exact_count(self):
        net=parity_network('pair2',4)
        expected,_=independent_count('pair2',4)
        values=[]
        for streaming in (False,True):
            c=ContractionEngine(ContractorConfig(net.edges, net.edges+3, schedule='geometry64', recovery=RecoveryConfig(method='jet', streaming=streaming), leaf=LeafConfig(strategy='eliminate'), micro_active_depth=1))
            values.append(c.contract(net))
        self.assertEqual(values[0],values[1])
        self.assertEqual(values[0][0],expected)



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.integration
