from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
"""Independent checks for the v8 objective-preserving packer and leaf cutoff."""
import unittest
from itertools import product
from time import perf_counter
from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.packing import balanced_labels, pack, audit_packing
from non_exponential_sudoku.contraction.children import child_edge_audit
from non_exponential_sudoku.sudoku.three_cnf import Puzzle, TensorGraph
from reference.bounded_sudoku import from_tensor_graph
from reference.real_sudoku_bench import puzzles, independent_count_sparse
from reference.local_support import pin_band_wires


def degree_four_parallel(count=128, degree=4):
    def unit(bits, ring): return ring.one
    left, right = [], []
    for k in range(count):
        ports = tuple(range(k * degree, (k + 1) * degree))
        left.append(Vertex(f'L{k}', ports, unit))
        right.append(Vertex(f'R{k}', ports, unit))
    return Network(left, right, count * degree)


def to_integer(labels, r):
    return [sum(d * (r ** i) for i, d in enumerate(label)) for label in labels]


class BalancedTieBreaking(unittest.TestCase):
    def test_all_64_groups_are_balanced_on_512_wire_network(self):
        net = degree_four_parallel()
        corrected = pack(net, 64, 2)
        geometry = audit_packing(net, corrected)
        for key in ('all_edges_packed_exactly_once', 'orientation_geometry_valid',
                    'packet_bound_met', 'group_load_bound_met'):
            self.assertTrue(geometry[key], (key, geometry))
        self.assertEqual(geometry['packet_count'], 128)
        for i in range(2):
            child = child_edge_audit(net, corrected, i)
            self.assertTrue(child['exact_port_conservation'])
            self.assertTrue(child['paper_shrinkage_satisfied'])
            self.assertEqual(child['max_child_edges'], 16)
        numeric = pack(net, 64, 2, balanced_labels(net, 64, 2, tie_break='numeric'))
        self.assertFalse(audit_packing(net, numeric)['group_load_bound_met'])
        self.assertFalse(child_edge_audit(net, numeric, 1)['paper_shrinkage_satisfied'])

    def test_spread_labels_minimize_unchanged_conditional_objective(self):
        # After the first 4 distinct labels the label alphabet is exhausted,
        # exercising BOTH the zero-score fresh case and the overlap scorer.
        net = degree_four_parallel(count=9, degree=1)
        r, a = 2, 2
        N = r**a
        left, right = balanced_labels(net, r, a)
        left_ids = to_integer(left, r)
        right_ids = to_integer(right, r)
        # On this disjoint-edge graph, left pair costs are all 1. A new label
        # has cost 0; after exhaustion any label with smallest occupancy wins.
        for j, chosen in enumerate(left_ids):
            costs = [sum(int(k == left_ids[w]) for w in range(j)) for k in range(N)]
            self.assertEqual(costs[chosen], min(costs))
        # All left endpoints have degree 1. Right-side overlap is 1 exactly
        # when two right vertices attach to the same left-label class.
        for j, chosen in enumerate(right_ids):
            costs = [sum(int(k == right_ids[w]) * int(left_ids[j] == left_ids[w])
                         for w in range(j)) for k in range(N)]
            self.assertEqual(costs[chosen], min(costs))
        self.assertEqual(left[0], (0, 0))
        self.assertEqual(left[1], (1, 1))
        self.assertEqual(len(set(left_ids[:N])), N)

    def test_greedy_optimum_on_random_bipartite_multigraphs(self):
        # Exhaustively evaluate every candidate label against a separate
        # conditional-expectation score implementation, including parallel
        # edges, shared endpoints, and cases with more vertices than labels.
        import random
        from collections import Counter
        rng = random.Random(20261107)
        r, a, choices = 2, 2, 4
        def unit(bits, ring): return ring.one
        for _ in range(35):
            nl, nr = rng.randrange(2, 9), rng.randrange(2, 9)
            m = rng.randrange(1, 24)
            left_ports = [[] for _ in range(nl)]
            right_ports = [[] for _ in range(nr)]
            for edge in range(m):
                lv,rv = rng.randrange(nl),rng.randrange(nr)
                left_ports[lv].append(edge)
                right_ports[rv].append(edge)
            net = Network([Vertex(f'L{i}',tuple(p),unit)
                           for i,p in enumerate(left_ports)],
                          [Vertex(f'R{i}',tuple(p),unit)
                           for i,p in enumerate(right_ports)],m)
            net.validate()
            ll, rr = balanced_labels(net,r,a)
            left_ids, right_ids = to_integer(ll,r), to_integer(rr,r)
            lh = [Counter(next(j for j,p in enumerate(right_ports) if e in p)
                          for e in ports) for ports in left_ports]
            for j in range(nl):
                scores = []
                for k in range(choices):
                    total = 0
                    for w in range(j):
                        shared = sum(q * lh[w][endpoint] for endpoint,q in lh[j].items())
                        wt = len(left_ports[j])*len(left_ports[w])+(choices-1)*shared
                        if left_ids[w]==k:total+=wt
                    scores.append(total)
                self.assertEqual(scores[left_ids[j]],min(scores))
            rh = [Counter(left_ids[next(i for i,p in enumerate(left_ports) if e in p)]
                          for e in ports) for ports in right_ports]
            for j in range(nr):
                scores=[]
                for k in range(choices):
                    total=0
                    for w in range(j):
                        overlap=sum(q*rh[w][lid] for lid,q in rh[j].items())
                        if right_ids[w]==k:total+=overlap
                    scores.append(total)
                self.assertEqual(scores[right_ids[j]],min(scores))

    def test_bijective_prefix_for_three_coordinates(self):
        # A 3-coordinate ring must spread its initial r labels in EVERY
        # coordinate while never repeating a complete label.
        net = degree_four_parallel(count=27, degree=1)
        left, right = balanced_labels(net, 3, 3)
        for side in (left, right):
            self.assertEqual(len(set(side)), 27)
            for coordinate in range(3):
                self.assertEqual({x[coordinate] for x in side[:3]}, {0, 1, 2})
                self.assertEqual([sum(x[coordinate] == j for x in side) for j in range(3)],
                                 [9, 9, 9])


class GeneralizedSudokuGeometry(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.puzzle = Puzzle(2, (0,) * 16)
        cls.formula = cls.puzzle.encode()
        cls.graph = TensorGraph.from_cnf(cls.formula)
        cls.net = from_tensor_graph(cls.graph)

    def test_exact_degree_three_adapter_on_known_witness(self):
        from reference.generalized_bench import canonical_solution
        witness = self.puzzle.witness(self.formula, canonical_solution(2))
        bits = self.graph.witness_edges(self.formula, witness)
        ring = Padic(5, modulus_polynomial(5), 5)
        self.assertEqual(self.graph.evaluate(bits), 1)
        result = ring.one
        for vertex in self.net.left + self.net.right:
            result = ring.mul(result, vertex.oracle(tuple(int(bits[e]) for e in vertex.ports), ring))
        self.assertEqual(result, ring.one)
        self.assertEqual(max(len(v.ports) for v in self.net.left + self.net.right), 3)

    def test_exact_vertex_truth_tables_match_independent_tensor_graph(self):
        from itertools import product
        ring=Padic(5,modulus_polynomial(5),5)
        mapped={int(v.name.split(':')[1]):v for v in self.net.left+self.net.right}
        self.assertEqual(len(mapped),len(self.graph.vertices))
        for index,(kind,ports,payload) in enumerate(self.graph.vertices):
            vertex=mapped[index]
            self.assertEqual(vertex.ports,ports)
            for bits in product((0,1),repeat=len(ports)):
                if kind=='clause':
                    expected=int(any((bit==1) if sign>0 else (bit==0)
                                     for bit,sign in zip(bits,payload)))
                elif kind=='copy':
                    expected=2 if not bits else int(all(v==bits[0] for v in bits))
                elif kind=='link':
                    expected=int(bits[0]==bits[1])
                else:raise AssertionError(kind)
                self.assertEqual(vertex.oracle(bits,ring),ring.scalar(expected))

    def test_real_4x4_bounded_degree_graph_shrinks_but_packet_bound_fails(self):
        net = self.net
        self.assertEqual(net.edges, 2880)
        corrected = pack(net, 64, 2)
        p = audit_packing(net, corrected)
        self.assertTrue(p['all_edges_packed_exactly_once'])
        self.assertTrue(p['orientation_geometry_valid'])
        self.assertTrue(p['group_load_bound_met'])
        # The theorem's PACKET-count sufficient condition fails at this size.
        # It would be incorrect to label this a paper-admissible execution.
        self.assertFalse(p['packet_bound_met'])
        children = [child_edge_audit(net, corrected, i) for i in range(2)]
        for child in children:
            self.assertTrue(child['exact_port_conservation'])
            self.assertTrue(child['paper_shrinkage_satisfied'])
            self.assertLessEqual(child['max_child_edges'], 96)
        numeric = pack(net, 64, 2, balanced_labels(net, 64, 2, tie_break='numeric'))
        self.assertFalse(child_edge_audit(net, numeric, 1)['paper_shrinkage_satisfied'])


class ExactLeafCutoff(unittest.TestCase):
    def test_optional_cutoff_retains_exact_two_level_sudoku_count(self):
        name, puzzle, expected = next((name,p,count) for name,p,count in puzzles()
                                      if name == '9x9-77-givens-two-solutions')
        self.assertEqual(independent_count_sparse(puzzle, 8), expected)
        net, _ = pin_band_wires(puzzle)
        values = []
        for cutoff in (0, 8):
            calc = ContractionEngine(ContractorConfig(net.edges, net.edges+2, schedule='micro', recovery=RecoveryConfig(method='jet'), leaf=LeafConfig(strategy='eliminate', adaptive_limit=cutoff), micro_active_depth=2))
            values.append(calc.contract(net))
            self.assertEqual(values[-1][0], expected)
            if cutoff:
                self.assertGreater(calc.stats.adaptive_leaf_cutoffs, 0)
                self.assertNotIn(2, calc.stats.depth_counts)
            else:
                self.assertGreater(calc.stats.depth_counts.get(2, 0), 0)
        self.assertEqual(values[0], values[1])

    def test_paper_schedule_does_not_change_when_cutoff_enabled(self):
        from non_exponential_sudoku.core.network import simple_network
        net = simple_network(1, [((0,), {(1,):1})], [((0,), {(1,):1})])
        a = ContractionEngine(ContractorConfig(1, 4, schedule='paper', leaf=LeafConfig(limit=4, strategy='eliminate')))
        b = ContractionEngine(ContractorConfig(1, 4, schedule='paper', leaf=LeafConfig(limit=4, strategy='eliminate', adaptive_limit=4)))
        self.assertEqual(a.contract(net), b.contract(net))
        self.assertEqual(b.stats.adaptive_leaf_cutoffs,0)

if __name__ == '__main__': unittest.main()


# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.extended
