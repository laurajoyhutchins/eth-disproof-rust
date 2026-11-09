"""Independent input-encoding and paper-recursion regression fixtures."""
import random
import unittest
from itertools import permutations,product
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.band_network import BandNetwork
from reference.generalized_bench import canonical_solution
from reference.real_sudoku_bench import puzzles, independent_count_sparse
from reference.local_support import matching_possible, projected_domains, pin_band_wires, LocalContradiction
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.network import eliminate_leaf, simple_network
from non_exponential_sudoku.core.packing import balanced_labels
from non_exponential_sudoku.runtime.budget import CapacityError
from reference.sudoku_paper_solver import solve, paper_count


class BandEncodingTests(unittest.TestCase):
    def test_one_to_one_witness_for_four_sizes(self):
        for b in (1,2,3,4):
            with self.subTest(box=b):
                n=b*b;p=Puzzle(b,(0,)*(n*n))
                graph=BandNetwork.from_puzzle(p)
                w=canonical_solution(b)
                self.assertEqual(graph.net.edges,n*n*max(1,(n-1).bit_length()))
                self.assertEqual(graph.evaluate(graph.witness_edges(w)),1)
                self.assertEqual(graph.summary()['direct_wires'],3*graph.net.edges)
    def test_independently_enumerated_4x4_grids(self):
        p=Puzzle(2,(0,)*16);g=BandNetwork.from_puzzle(p)
        rows=list(permutations((1,2,3,4)))
        accepted=0
        for a in rows:
            for b in rows:
                # Early row/box screen still verifies the final puzzle on its
                # own; no tensor code produces reference solutions.
                if any(set(a[j:j+2]+b[j:j+2])!={1,2,3,4} for j in (0,2)):
                    continue
                for c in rows:
                    for d in rows:
                        digits=a+b+c+d
                        if p.valid_solution(digits):
                            self.assertEqual(g.evaluate(g.witness_edges(digits)),1)
                            accepted+=1
        self.assertEqual(accepted,288)
    def test_bogus_assignments_are_rejected(self):
        p=Puzzle(2,(0,)*16);g=BandNetwork.from_puzzle(p)
        rng=random.Random(402)
        for _ in range(120):
            x=tuple(rng.randint(1,4) for _ in range(16))
            self.assertEqual(g.evaluate(g.witness_edges(x)),int(p.valid_solution(x)))


class SupportReductionTests(unittest.TestCase):
    def test_matching_against_exhaustive_permutations(self):
        perms=list(permutations(range(4)))
        rng=random.Random(210)
        for _ in range(150):
            domains=[rng.randrange(1,16) for _ in range(4)]
            expected=any(all(domains[c]&(1<<d) for c,d in enumerate(perm))
                         for perm in perms)
            self.assertEqual(matching_possible(domains,4),expected)
    def test_2_and_4_solution_fixtures_support_counts(self):
        names={'4x4-12-givens-two-solutions','9x9-77-givens-two-solutions',
               '16x16-252-givens-two-solutions','4x4-8-givens-four-solutions',
               '9x9-73-givens-four-solutions'}
        for name,p,expected in puzzles():
            if name not in names:continue
            with self.subTest(name=name):
                self.assertEqual(independent_count_sparse(p),expected)
                n,info=pin_band_wires(p)
                self.assertEqual(n.edges,4 if expected==2 else 8)
                self.assertEqual(info['original_wires'],p.side**2*max(1,(p.side-1).bit_length()))
    def test_conflicting_clues_are_detected(self):
        p=Puzzle.from_text('11'+'.'*14,2)
        with self.assertRaises(LocalContradiction):pin_band_wires(p)


class GenuineRecursionTests(unittest.TestCase):
    def test_exact_count_and_witness_multiple_sizes(self):
        names={'4x4-12-givens-two-solutions','9x9-77-givens-two-solutions',
               '16x16-252-givens-two-solutions'}
        for name,p,expected in puzzles():
            if name not in names:continue
            with self.subTest(name=name):
                result=solve(p)
                self.assertEqual(result['count'],expected)
                self.assertEqual(result['status'],'solved')
                self.assertGreater(result['root'].get('mode_dp_local_child_evaluations',0),0)
                solution=tuple('123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'.index(ch)+1
                               for ch in result['solution'])
                self.assertTrue(p.valid_solution(solution))
    def test_four_exact_solutions_9x9(self):
        p=next(p for name,p,expected in puzzles()
               if name=='9x9-73-givens-four-solutions')
        count,stats=paper_count(p)
        self.assertEqual(count,4)
        self.assertEqual(stats['interpolation_evaluations'],50)
        self.assertGreater(stats['child_networks'],0)
    def test_hard_puzzle_is_explicit_capacity_refusal(self):
        p=next(p for name,p,expected in puzzles() if name=='9x9-hard-unique')
        _,info=pin_band_wires(p)
        self.assertEqual(info['remaining_wires'],177)
        with self.assertRaises(CapacityError):paper_count(p)


class LeafAndLabelTests(unittest.TestCase):
    def test_leaf_elimination_matches_enumeration(self):
        rng=random.Random(211)
        R=Padic(4,modulus_polynomial(4),6)
        for n in range(1,7):
            for rep in range(12):
                sides=[]
                for side in range(2):
                    groups=[[] for _ in range(3)]
                    for e in range(n):groups[rng.randrange(3)].append(e)
                    sides.append([(ports,{bits:rng.randrange(3)
                                          for bits in product((0,1),repeat=len(ports))})
                                  for ports in groups])
                graph=simple_network(n,*sides)
                self.assertEqual(eliminate_leaf(graph,R,12),graph.direct(R,12))
    def test_labels_respect_original_full_objective(self):
        rng=random.Random(5)
        for n in range(1,8):
            left=[[] for _ in range(3)];right=[[] for _ in range(3)]
            for e in range(n):
                left[rng.randrange(3)].append(e)
                right[rng.randrange(3)].append(e)
            graph=simple_network(n,
                  [(ports,{bits:1 for bits in product((0,1),repeat=len(ports))})
                   for ports in left],
                  [(ports,{bits:1 for bits in product((0,1),repeat=len(ports))})
                   for ports in right])
            # All label assignments are valid; the greedy result is stable.
            a=balanced_labels(graph,2,1)
            self.assertEqual(a,balanced_labels(graph,2,1))
            self.assertEqual(len(a[0]),3)
            self.assertEqual(len(a[1]),3)



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.integration
