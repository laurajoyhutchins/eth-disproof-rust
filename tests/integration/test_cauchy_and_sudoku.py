import unittest
from itertools import product
from fractions import Fraction
from non_exponential_sudoku.sudoku.three_cnf import Puzzle, TensorGraph, CNF
from non_exponential_sudoku.sudoku.direct_network import DirectNetwork
from reference.paper_algebra import cauchy_kernel, eval_poly, hermite_at_zero, jet, direct_cauchy_deformation, cauchy_deform_direct_sudoku

EXAMPLE = ('534678912' '672195348' '198342567'
           '859761423' '426853791' '713924856'
           '961537284' '287419635' '345286179')
SOLUTION4 = '1234341221434321'

class ExactReductionTests(unittest.TestCase):
    def test_one_by_one_exact_count(self):
        for s in ('.','1'):
            p=Puzzle.from_text(s,1)
            f=p.encode()
            self.assertEqual(f.nvars,1)
            self.assertEqual(sum(f.satisfied([False,*xs]) for xs in product((False,True), repeat=f.nvars)),1)

    def test_two_by_two_solving_assigned_grid(self):
        p=Puzzle.from_text(SOLUTION4,2)
        self.assertTrue(p.valid_solution(tuple(map(int,SOLUTION4))))
        f=p.encode()
        self.assertTrue(all(len(cl)<=3 for cl in f.clauses))
        bits=p.witness(f,tuple(map(int,SOLUTION4)))
        self.assertTrue(f.satisfied(bits))
        graph=TensorGraph.from_cnf(f)
        graph.validate()
        self.assertTrue(all(len(ports)<=3 for _,ports,_ in graph.vertices))
        self.assertEqual(graph.evaluate(graph.witness_edges(f,bits)),1)
        bits[f.primary[0,0,2]]=True
        self.assertFalse(f.satisfied(bits))

    def test_nine_by_nine_parsimonious_witness(self):
        p=Puzzle.from_text(EXAMPLE,3)
        self.assertTrue(p.valid_solution(tuple(map(int,EXAMPLE))))
        f=p.encode()
        bits=p.witness(f,tuple(map(int,EXAMPLE)))
        self.assertTrue(f.satisfied(bits))
        graph=TensorGraph.from_cnf(f)
        graph.validate()
        self.assertEqual(graph.evaluate(graph.witness_edges(f,bits)),1)

    def test_unsatisfied_clues_are_detected(self):
        p=Puzzle.from_text('11'+'.'*79,3)
        f=p.encode()
        # Consistent with a completed valid Sudoku except for clue 2 in row 0.
        bits=p.witness(f,tuple(map(int, EXAMPLE)))
        self.assertFalse(f.satisfied(bits))

    def test_or_gate_uniquely_extends(self):
        f=CNF()
        a=f.var(); b=f.var(); z=f.or_gate(a,b)
        for av,bv in product((False,True),repeat=2):
            bits=f.extend({a:av,b:bv})
            self.assertEqual(sum(f.satisfied([False,av,bv,zv]) for zv in (False,True)),1)
            self.assertEqual(bits[z],av or bv)

class DirectPaperInputTests(unittest.TestCase):
    def test_empty_one_cell_has_one_completion(self):
        p=Puzzle.from_text('.',1)
        g=DirectNetwork.from_puzzle(p)
        self.assertEqual(g.edge_count,3)
        self.assertEqual(sum(g.evaluate(bits) for bits in product((0,1),repeat=3)),1)

    def test_deformed_direct_sudoku_one_cell(self):
        p=Puzzle.from_text('.',1)
        g=DirectNetwork.from_puzzle(p)
        pol=cauchy_deform_direct_sudoku(g)
        self.assertEqual(eval_poly(pol,0),1)
        L=4
        nodes=[t for t in range(-L,L) if t]
        multiplicity=(len(pol)+len(nodes)-1)//len(nodes)
        self.assertEqual(hermite_at_zero([(t,jet(pol,t,multiplicity)) for t in nodes]),1)

    def test_nine_by_nine_tensor_wires(self):
        p=Puzzle.from_text(EXAMPLE,3)
        g=DirectNetwork.from_puzzle(p)
        self.assertEqual(g.edge_count,972)
        self.assertEqual(max(len(v.ports) for v in g.vertices),36)
        bits=g.witness_edges(tuple(map(int,EXAMPLE)))
        self.assertEqual(g.evaluate(bits),1)
        invalid=list(map(int,EXAMPLE))
        invalid[0]=invalid[1]  # duplicated number in row
        self.assertEqual(g.evaluate(g.witness_edges(tuple(invalid))),0)

    def test_four_by_four_tensor_and_clues(self):
        puzzle=Puzzle.from_text(SOLUTION4,2)
        graph=DirectNetwork.from_puzzle(puzzle)
        self.assertEqual(graph.edge_count,96)
        self.assertEqual(graph.evaluate(graph.witness_edges(tuple(map(int,SOLUTION4)))),1)
        wrong=list(map(int,SOLUTION4)); wrong[0]=2
        self.assertEqual(graph.evaluate(graph.witness_edges(tuple(wrong))),0)

class PaperAlgebraTests(unittest.TestCase):
    def test_cauchy_at_zero_identity(self):
        for L in (1,2,3,4):
            for x in range(L):
                for y in range(L):
                    self.assertEqual(eval_poly(cauchy_kernel(L,x,y),0),int(x == y))

    def test_cauchy_at_nodes_is_diagonal_shift(self):
        for L in (2,3):
            for t in range(-L,L):
                for x in range(L):
                    for y in range(L):
                        value = eval_poly(cauchy_kernel(L,x,y),t)
                        if y-x != t:
                            self.assertEqual(value,0)

    def test_cauchy_deformed_contraction_matches_cnf(self):
        # Genuine paper F(T), evaluated by direct sum on micro-instances.
        examples = [
            (1, [(1,)], 1),
            (1, [(1,),(-1,)], 0),
            (2, [(1,2)], 3),
            (2, [(1,),(2,)], 1),
            (1, [(-1,)], 1),
        ]
        for n, clauses, expected in examples:
            f = CNF(nvars=n,clauses=[tuple(x) for x in clauses])
            g = TensorGraph.from_cnf(f)
            self.assertEqual(sum(g.evaluate(edge_bits) for edge_bits in product((False,True),repeat=g.edges)),expected)
            deform = direct_cauchy_deformation(g)
            self.assertEqual(eval_poly(deform,0),expected)
            # Hermite jets away from zero reconstruct the same count.
            degree = len(deform)-1
            L=1 << (max(1,g.edges)-1).bit_length()
            nodes=[t for t in range(-L,L) if t]
            per_node=(degree+1+len(nodes)-1)//len(nodes)
            self.assertEqual(hermite_at_zero([(t,jet(deform,t,per_node)) for t in nodes]),expected)

    def test_exact_hermite_recovery(self):
        for pol in ([5], [3,2,-7], [10,3,8,2,-4,9]):
            from fractions import Fraction
            p=list(map(Fraction,pol))
            jets=[(1,jet(p,1,2)),(2,jet(p,2,3)),(3,jet(p,3,max(1,len(p)-5)))]
            self.assertEqual(hermite_at_zero(jets),p[0])



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.integration
