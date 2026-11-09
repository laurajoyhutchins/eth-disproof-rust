from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
"""Independent tests for nested, exact Taylor-jet recursive contraction."""
import random
import unittest
from itertools import product

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.network import simple_network
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.contraction.children import make_child
from non_exponential_sudoku.core.jets import JetRing, embed_element, precision_ring, flatten_element, unflatten_element


class NestedRingTests(unittest.TestCase):
    def setUp(self):
        self.base = Padic(5, modulus_polynomial(5), 13)

    def test_nested_inverse_and_nontrivial_cross_terms(self):
        outer = JetRing(self.base, 3)
        nested = JetRing(outer, 4)
        a = nested.add(nested.one, nested.variable)
        a = nested.add(a, embed_element(outer.variable, outer, nested))
        a = nested.add(a, nested.mul(nested.variable, embed_element(outer.variable, outer, nested)))
        self.assertEqual(nested.mul(a, nested.inv(a)), nested.one)
        self.assertNotEqual(nested.mul(nested.variable, embed_element(outer.variable, outer, nested)), nested.zero)

    def test_precision_lift_and_roundtrip_preserve_nested_shape(self):
        rng = random.Random(7317)
        for lengths in ((2,), (3, 2), (2, 3, 2)):
            ring = self.base
            for q in lengths:
                ring = JetRing(ring, q)
            coords = tuple(rng.randrange(1 << 13)
                           for _ in range(len(flatten_element(ring.zero, ring))))
            value = unflatten_element(coords, ring)
            self.assertEqual(flatten_element(value, ring), coords)
            lifted_ring = precision_ring(ring, 37)
            lifted = embed_element(value, ring, lifted_ring)
            self.assertEqual(flatten_element(lifted, lifted_ring), coords)
            wrapped = JetRing(lifted_ring, 4)
            self.assertEqual(embed_element(value, ring, wrapped),
                             (lifted,) + wrapped.zero[1:])

    def test_nested_ring_reduction_is_rejected(self):
        jet = JetRing(self.base, 3)
        with self.assertRaises(TypeError):
            embed_element(jet.one, jet, self.base)


class NestedContractionTests(unittest.TestCase):
    def test_nonconstant_parent_packet_tensor_survives_second_recovery(self):
        # The parent first constructs a packet tensor containing nonzero
        # z and z^2 terms. A second *active* recursion must preserve every
        # coefficient, not merely the integer value at z=0.
        net = simple_network(1,
            [([0], {(1,): 1})], [([0], {(1,): 1})])
        labels = (((0,),), ((0,),))
        contractor = ContractionEngine(ContractorConfig(1, 5, schedule='micro', recovery=RecoveryConfig(method='jet'), leaf=LeafConfig(strategy='eliminate'), micro_active_depth=2))
        parent = JetRing(Padic(contractor.e, contractor.f, 18), 3)
        packing = pack(net, 2, 1, labels)
        modes = mode_catalog(net, packing, 1, parent.p)
        self.assertFalse(modes)
        child = make_child(net, packing, modes, (), 1, parent.variable,
                           parent, 0, 0)
        direct = child.direct(parent, limit=5)
        self.assertNotEqual(direct[1], parent.base.zero)
        self.assertNotEqual(direct[2], parent.base.zero)
        actual = contractor.contract(child, precision=parent.p, depth=1,
                                     ring=parent)
        self.assertEqual(actual, direct)
        self.assertGreater(contractor.stats.depth_counts.get(2, 0), 0)

    def test_random_counting_matches_two_level_reference_interpolation(self):
        rng = random.Random(812)
        for n, repetitions in ((1, 3), (2, 3)):
            inputs = tuple(product((0, 1), repeat=n))
            for _ in range(repetitions):
                left = {x: rng.randrange(2) for x in inputs}
                right = {x: rng.randrange(2) for x in inputs}
                expected = sum(left[x] * right[x] for x in inputs)
                net = simple_network(n,
                    [(tuple(range(n)), left)], [(tuple(range(n)), right)])
                observed = []
                for method in ('jet', 'interpolate'):
                    contractor = ContractionEngine(ContractorConfig(n, n + 4, schedule='micro', recovery=RecoveryConfig(method=method), leaf=LeafConfig(strategy='eliminate'), root_labels=(((0,),), ((1,),)), micro_active_depth=2))
                    value = contractor.contract(net)
                    self.assertGreater(contractor.stats.depth_counts.get(2, 0), 0)
                    observed.append(value)
                self.assertEqual(observed[0], observed[1])
                self.assertEqual(observed[0][0], expected)

    def test_three_edge_precision_wrap_is_not_misclassified(self):
        n = 3
        values = {v: 1 for v in product((0, 1), repeat=n)}
        net = simple_network(3, [((0,1,2), values)], [((0,1,2), values)])
        count_mod_8 = ContractionEngine(ContractorConfig(3, 3, schedule='micro', recovery=RecoveryConfig(method='jet'), leaf=LeafConfig(strategy='eliminate'), micro_active_depth=2, root_labels=(((0,),), ((1,),))))
        self.assertEqual(count_mod_8.contract(net)[0], 0)
        count_mod_32 = ContractionEngine(ContractorConfig(3, 5, schedule='micro', recovery=RecoveryConfig(method='jet'), leaf=LeafConfig(strategy='eliminate'), micro_active_depth=2, root_labels=(((0,),), ((1,),))))
        self.assertEqual(count_mod_32.contract(net)[0], 8)



class SudokuTwoLevelIntegration(unittest.TestCase):
    def test_9x9_four_wire_count_is_exact_with_two_active_levels(self):
        from reference.real_sudoku_bench import puzzles, independent_count_sparse
        from reference.local_support import pin_band_wires
        _, puzzle, count = next((name, p, expected) for name,p,expected in puzzles()
                                if name == '9x9-77-givens-two-solutions')
        self.assertEqual(independent_count_sparse(puzzle, 10), count)
        network, _ = pin_band_wires(puzzle)
        self.assertEqual(network.edges, 4)
        solver = ContractionEngine(ContractorConfig(network.edges, network.edges+2, schedule='micro', recovery=RecoveryConfig(method='jet'), leaf=LeafConfig(strategy='eliminate'), micro_active_depth=2))
        self.assertEqual(solver.contract(network)[0], count)
        self.assertGreater(solver.stats.depth_counts.get(2, 0), 0)

class ResourceBudgetTests(unittest.TestCase):
    def test_nested_jet_coordinate_budget_rejects_before_expansion(self):
        net = simple_network(2,
            [((0,1), {(0,0):1})], [((0,1), {(0,0):1})])
        c = ContractionEngine(ContractorConfig(2, 5, schedule='micro', recovery=RecoveryConfig(method='jet', max_jet_coordinates=20), micro_active_depth=2))
        from non_exponential_sudoku.runtime.budget import CapacityError
        with self.assertRaisesRegex(CapacityError,'Nested jet needs'):
            c.contract(net)


# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.integration
