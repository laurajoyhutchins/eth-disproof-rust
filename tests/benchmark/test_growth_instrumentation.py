"""Instrumented growth must be exact, non-invasive, and budget-preserving."""
from __future__ import annotations
from non_exponential_sudoku.runtime.config import ModeLimits

import pytest
from benchmarks.growth_probe import GrowthCollector, RingOperationCounter, admissible_assignments
from benchmarks.growth_worker import measure
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.modes import Mode
from non_exponential_sudoku.runtime.statistics import Counters
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.elimination.engine import ModeEliminator

pytestmark = pytest.mark.checkpoint


def test_exact_weighted_assignment_bound():
    modes=[Mode(0,0,0,0,1,1,(),(0,)), Mode(1,0,0,1,2,2,(),(0,))]
    domains=[range(2),range(2)]
    assert admissible_assignments((0,1),modes,domains,2)==2
    assert admissible_assignments((0,1),modes,domains,4)==4
    assert admissible_assignments((),modes,domains,2)==1


def test_ring_instrumentation_restores_methods_after_exit_and_exception():
    R=Padic(5,modulus_polynomial(5),7)
    original=Padic.mul
    with RingOperationCounter() as counter:
        assert R.add(R.one,R.one)==R.scalar(2)
        assert R.mul(R.one,R.one)==R.one
        jet=JetRing(R,2)
        assert jet.add(jet.one,jet.zero)==jet.one
        assert counter.summary()['by_ring_method']['Padic.mul']==1
        assert counter.summary()['by_ring_method']['JetRing.add']==1
    assert Padic.mul is original
    with pytest.raises(ArithmeticError):
        with RingOperationCounter():
            raise ArithmeticError('test exception cleanup')
    assert Padic.mul is original


def test_sparse_grid_exact_and_upper_bounds():
    row=measure('grid-sparse',3)
    assert row['status']=='completed'
    assert row['observed_exact_count']=='2'
    growth=row['structural']
    assert growth['max_factor_scope']>=growth['max_planned_factor_scope']
    assert growth['peak_factor_rows']<=growth['max_admissible_factor_states_bound']
    assert growth['exact_direct_child_evaluations'] <= growth['planned_child_evaluations_upper_bound']
    assert growth['peak_simultaneous_retained_coefficients']>0
    assert row['ring_arithmetic']['all_ring_method_calls']>0


def test_observation_does_not_change_result_or_work():
    R=Padic(5,modulus_polynomial(5),6)
    modes=[Mode(0,0,0,0,1,1,(),(0,)), Mode(1,0,0,1,2,1,(),(0,))]
    groups={0,1,2}
    def child(g,scope,bits):
        return R.one if not bits or len(set(bits))<=1 else R.zero
    def evaluate(with_probe):
        stats=Counters()
        probe=GrowthCollector() if with_probe else None
        if probe is not None: stats.growth_probe=probe
        got=ModeEliminator(modes,groups,R,child,stats,CapacityError,
                join_strategy='sparse').run()
        return got, stats, probe
    plain,stats,_=evaluate(False)
    measured,measured_stats,probe=evaluate(True)
    assert plain==measured
    assert stats.mode_dp_operations==measured_stats.mode_dp_operations
    assert stats.mode_dp_local_child_evaluations==measured_stats.mode_dp_local_child_evaluations
    assert len(probe.records)==1


def test_capacity_refusal_remains_capacity_refusal_with_probe():
    R=Padic(5,modulus_polynomial(5),9)
    modes=[Mode(j,0,0,0,1,1,(),(0,)) for j in range(7)]
    stats=Counters()
    probe=GrowthCollector()
    stats.growth_probe=probe
    with pytest.raises(CapacityError, match='factor size limit'):
        ModeEliminator(modes,{0,1},R,lambda *args:R.one,stats,CapacityError,
            limits=ModeLimits(max_factor_states=16)).run()
    assert not probe.frames
    assert probe.records[0]['status']=='refused_or_failed'
    assert probe.records[0]['max_planned_scope']==7
