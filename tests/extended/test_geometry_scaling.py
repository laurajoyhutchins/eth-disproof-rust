from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
"""Independent v9 scaling regression, no algorithmic performance assumptions."""
import unittest
from itertools import product

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.contraction.children import make_child
from reference.scaling_experiment import parity_network, independent_count, independent_gf2_count, topology_child, check_topology_against_real_child, geometry_one, mode_catalog_projection, precision_budget


class ExactStructuralIdentity(unittest.TestCase):
    def test_child_port_incidence_matches_real_make_child_both_coordinates(self):
        ring=Padic(5,modulus_polynomial(5),7)
        for family in ('cycle2','ladder3','pair2'):
            for span in (1,2,4,8):
                net=parity_network(family,span)
                packed=pack(net,64,2)
                for coordinate in (0,1):
                    groups=sorted(set(label[coordinate] for label in
                                      packed.groups_left+packed.groups_right))
                    for group in groups[:4]:
                        real=make_child(net,packed,[],(),1,ring.zero,ring,group,coordinate)
                        top=topology_child(net,packed,group,coordinate)
                        self.assertEqual(real.edges,top.edges)
                        self.assertEqual([v.ports for v in real.left],[v.ports for v in top.left])
                        self.assertEqual([v.ports for v in real.right],[v.ports for v in top.right])
                        self.assertEqual(len(real.right),len(packed.packets))

    def test_mode_projection_matches_exact_catalog(self):
        for family in ('cycle2','ladder3','pair2'):
            for span in (1,2,3,4,8):
                net=parity_network(family,span)
                packed=pack(net,64,2)
                for p in (3,7,11):
                    projection=mode_catalog_projection(net,packed,p)
                    modes=mode_catalog(net,packed,1,p,max_modes=20000)
                    self.assertEqual(projection['exact_descriptor_count'],len(modes))
                    self.assertEqual(projection['weight_one_modes'],sum(x.weight==1 for x in modes))

    def test_two_full_geometry_levels_genuinely_shrink_some_fixtures(self):
        for family, span in [('cycle2',32),('ladder3',32)]:
            case=geometry_one(family,span,depth=2)
            self.assertEqual([x['input_nodes'] for x in case['level_audits']][0],1)
            self.assertTrue(all(level['wire_conservation_all'] for level in case['level_audits']))
            self.assertTrue(case['level_audits'][0]['shrinkage_bound_all'])
            # Once child networks become tiny, integer degree/port loads
            # prevent the paper's 3M/32 bound from holding on every child.
            self.assertFalse(case['level_audits'][1]['shrinkage_bound_all'])
            self.assertLess(case['level_audits'][0]['largest_child_wires'],case['wires'])
            self.assertLess(case['level_audits'][1]['largest_child_wires'],
                            case['level_audits'][0]['largest_child_wires']+1)
            self.assertFalse(case['full_contraction_run'])

    def test_root_48_wire_pair_satisfies_all_local_packing_bounds(self):
        net=parity_network('pair2',24)
        from non_exponential_sudoku.core.packing import audit_packing
        from non_exponential_sudoku.contraction.children import child_edge_audit
        packed=pack(net,64,2)
        audit=audit_packing(net,packed)
        self.assertTrue(all(audit[k] for k in
            ('all_edges_packed_exactly_once','orientation_geometry_valid',
             'packet_bound_met','group_load_bound_met')))
        self.assertTrue(all(child_edge_audit(net,packed,i)['paper_shrinkage_satisfied']
                            for i in (0,1)))
        self.assertEqual(mode_catalog_projection(net,packed,120*net.edges+net.edges+3)['exact_descriptor_count'],0)

    def test_precision_formula_matches_experimental_recurrence(self):
        p=precision_budget(128,8,28)
        self.assertEqual(p['base_precision_bits'],131)
        self.assertEqual(p['first_precision_bits'],15491)
        self.assertEqual(p['second_precision_bits'],16451)
        self.assertEqual(p['first_jet_length'],384)
        self.assertEqual(p['nested_jet_ring_coordinates'],28*384*24)


class ActualRecursiveExecution(unittest.TestCase):
    def test_real_64_group_parity_networks(self):
        for family,span in (('cycle2',1),('ladder3',1),('pair2',8)):
            net=parity_network(family,span)
            expected,_=independent_count(family,span)
            contractor=ContractionEngine(ContractorConfig(net.edges, net.edges+3, schedule='geometry64', recovery=RecoveryConfig(method='jet'), leaf=LeafConfig(strategy='eliminate', limit=24), micro_active_depth=1))
            result=contractor.contract(net)
            self.assertEqual(result[0],expected)
            self.assertEqual(result[1:],(0,)*(len(result)-1))
            self.assertEqual(contractor.stats.active_depth_counts,{0:1})
            self.assertGreater(contractor.stats.child_networks,0)
            self.assertEqual(contractor.stats.recursive_calls,
                             contractor.stats.child_networks+1)


if __name__=='__main__':
    unittest.main()


# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.extended
