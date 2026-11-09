from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
"""Paper-parameter audit and finite, real 64-group geometry checks."""
import unittest
from itertools import product
from reference.schedule import audit_power_of_two, log2_ceil, at_least_power_of_two
from reference.sudoku_network_oracle import port_graph_with_cross_mode
from non_exponential_sudoku.core.packing import pack, audit_packing
from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.contraction.children import child_edge_audit, make_child, ceil_ninth_tenths
from non_exponential_sudoku.core.modes import mode_catalog, Mode, weighted_tuples
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.contraction.engine import paper_schedule_parameters


class PaperScheduleAudits(unittest.TestCase):
    def test_small_input_is_not_asymptotically_admissible(self):
        audit=audit_power_of_two(10)
        self.assertEqual(len(audit.levels),0)
        self.assertFalse(audit.all_active_obligations_pass)
        self.assertIn('u_d_zero',audit.stopping_reason)

    def test_near_first_nontrivial_parameters_not_asymptotically_admissible(self):
        audit=audit_power_of_two(524300)
        self.assertEqual(len(audit.levels),3)
        self.assertFalse(audit.all_active_obligations_pass)
        self.assertTrue(all(lev.packet_count_bound for lev in audit.levels))
        self.assertTrue(all(lev.group_degree_bound for lev in audit.levels))
        self.assertFalse(all(lev.u_large_enough_for_asymptotic_proof for lev in audit.levels))

    def test_literal_64_group_full_asymptotic_schedule(self):
        # Deliberately symbolic: s = 2**(2**600) cannot be materialized.
        audit=audit_power_of_two(1<<600)
        self.assertTrue(audit.all_active_obligations_pass)
        self.assertEqual(len(audit.levels),100)
        self.assertEqual(audit.terminal_depth,100)
        self.assertEqual(audit.levels[0].depth,0)
        self.assertEqual(audit.levels[-1].depth,99)
        self.assertEqual(audit.levels[-1].child_ratio_num,3)
        self.assertEqual(audit.levels[-1].child_ratio_den,32)
        self.assertTrue(all(lev.all_checked() for lev in audit.levels))
        self.assertFalse(audit.full_execution_performed)

    def test_symbolic_schedule_matches_independent_live_parameter_code(self):
        # Instantiate no enormous extension ring. Compare the independent
        # exact schedule calculator to the *live* contractor params function.
        lam=524300
        symbolic=audit_power_of_two(lam)
        for level in symbolic.levels:
            r,a,u,H=paper_schedule_parameters(1 << lam, lam, level.depth)
            self.assertEqual(r,64)
            self.assertEqual(a,level.a)
            self.assertEqual(u,level.u)
            self.assertGreaterEqual(H,1<<symbolic.H_lower_log2)
            self.assertLess(H,1<<symbolic.H_upper_log2)

    def test_exact_integer_degree_not_float(self):
        for n in (1,2,3,27,972,10**50):
            got=ceil_ninth_tenths(n)
            self.assertGreaterEqual(got**10,n**9)
            if got>1:self.assertLess((got-1)**10,n**9)
        self.assertTrue(at_least_power_of_two(3,8))
        self.assertFalse(at_least_power_of_two(3,9))
        self.assertEqual(log2_ceil(9),4)


class ActualChildGeometry(unittest.TestCase):
    def test_real_64_group_4_slot_packet_child_reduction(self):
        # Thirty-two disjoint unordered symbol pairs, four orientations,
        # and four wires per orientation. No symbolic/certificate shortcut.
        # This construction satisfies the *packing conclusions* but is not
        # large enough for the paper's sufficient parameter hypotheses.
        left=[];right=[];label_l=[];label_r=[]
        index=0
        def unit(bits,R):return R.one
        for lo in range(0,64,2):
            hi=lo+1
            for x0,x1 in product((0,1),repeat=2):
                l=(hi if x0 else lo,hi if x1 else lo)
                r=(lo if x0 else hi,lo if x1 else hi)
                for _ in range(4):
                    left.append(Vertex(f'L{index}',(index,),unit))
                    right.append(Vertex(f'R{index}',(index,),unit))
                    label_l.append(l); label_r.append(r)
                    index+=1
        net=Network(left,right,index)
        self.assertEqual(net.edges,512)
        labels=(tuple(label_l),tuple(label_r))
        pk=pack(net,64,2,labels)
        geometry=audit_packing(net,pk)
        for key in ('all_edges_packed_exactly_once','orientation_geometry_valid',
                    'packet_bound_met','group_load_bound_met'):
            self.assertTrue(geometry[key],(key,geometry))
        self.assertEqual(geometry['packet_count'],128)
        for coordinate in (0,1):
            audit=child_edge_audit(net,pk,coordinate)
            self.assertTrue(audit['paper_shrinkage_satisfied'])
            self.assertTrue(audit['exact_port_conservation'])
            self.assertEqual(audit['total_child_edges'],1024)
            self.assertEqual(audit['max_child_edges'],16)
        R=Padic(5,modulus_polynomial(5),5)
        modes=mode_catalog(net,pk,1,R.p,max_modes=5000)
        self.assertTrue(modes)
        beta=(0,)*len(modes)
        for group in range(64):
            child=make_child(net,pk,modes,beta,1,R.one,R,group,0)
            self.assertEqual(child.edges,16)
            self.assertLessEqual(max(len(v.ports) for v in child.right),8)

    def test_64_group_full_contraction_identity_on_finite_network(self):
        net=port_graph_with_cross_mode()
        calc=ContractionEngine(ContractorConfig(1, 3, schedule='geometry64', root_labels=(((0,0),),((1,0),))))
        self.assertEqual(calc.contract(net)[0],1)
        self.assertGreater(calc.stats.mode_dp_local_child_evaluations,0)
        self.assertGreater(calc.stats.skipped_empty_groups,0)
        self.assertGreater(calc.stats.depth_counts.get(1,0),0)

    def test_long_mode_iterator_is_not_recursive(self):
        # 1,200 mode descriptors whose row degree is zero. The only
        # legal choice is beta=0. A recursive Python generator would
        # fail at its default 1,000-frame interpreter recursion limit.
        mode=Mode(0,0,0,0,1,1,(),())
        out=list(weighted_tuples([mode]*1200,5))
        self.assertEqual(len(out),1)
        self.assertEqual(len(out[0]),1200)
        self.assertEqual(sum(out[0]),0)



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.extended
