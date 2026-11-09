"""Fast differential checks: no full expensive correctness suite at checkpoint."""
from __future__ import annotations
from dataclasses import replace
from itertools import product
import random
import pytest
from non_exponential_sudoku import *
from non_exponential_sudoku.core.network import eliminate_leaf
from non_exponential_sudoku.contraction.children import make_child
from non_exponential_sudoku.contraction.compiled_children import CompiledChildPlan
from non_exponential_sudoku.contraction.packets import EvaluationContext
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.sudoku.encoding import port_graph_with_cross_mode
from benchmarks.recursive_cases import get_case

pytestmark=pytest.mark.checkpoint

@pytest.mark.requires_native
@pytest.mark.parametrize('variant',['reference','plans','packet','leaf','combined','memo','memo-all'])
def test_exact_micro_recursion_with_independent_parity(variant):
    pytest.importorskip('native_recursive')
    result,stats=get_case('parity-2wire',variant).validate()
    assert result==2
    if variant=='memo-all':
        assert stats.packet_entry_memo_misses>0

@pytest.mark.requires_native
@pytest.mark.parametrize('variant',['reference','combined','memo-all'])
def test_nested_two_active_levels(variant):
    pytest.importorskip('native_recursive')
    result,stats=get_case('nested-2wire',variant).validate()
    assert result==4
    assert stats.depth_counts.get(2,0)>0

@pytest.mark.requires_native
@pytest.mark.parametrize('variant',['reference','combined','memo-all'])
def test_exact_mode_crossing(variant):
    pytest.importorskip('native_recursive')
    result,stats=get_case('crossing-4wire',variant).validate()
    assert result==16
    assert stats.mode_dp_local_child_evaluations>0


@pytest.mark.requires_native
def test_compiled_child_matches_reference_tables_and_lifting():
    pytest.importorskip('native_recursive')
    net=port_graph_with_cross_mode()
    packing=pack(net,2,1,(((0,),),((1,),)))
    for precision in (9,17):
      B=Padic(5,modulus_polynomial(5),precision)
      outer=JetRing(B,3)
      for R in (B,JetRing(outer,2)):
       for t in (-1,1):
        modes=mode_catalog(net,packing,t,R.p)
        reference_context=EvaluationContext(t,R.one,R,1,native_packet=False)
        native_context=EvaluationContext(t,R.one,R,1,native_packet=True,packet_memo_entries=32)
        for beta in (tuple(0 for _ in modes), tuple(1 for _ in modes)):
         for g in (0,1):
          expected=make_child(net,packing,modes,beta,t,R.one,R,g,0,reference_context)
          got=CompiledChildPlan(net,packing,g,0).instantiate(modes,beta,t,R.one,R,native_context)
          assert expected.edges==got.edges
          assert [v.ports for v in expected.left+expected.right]==[v.ports for v in got.left+got.right]
          for a,b in zip(expected.right,got.right):
           for bits in product((0,1),repeat=len(a.ports)):
            assert a.oracle(bits,R)==b.oracle(bits,R)


@pytest.mark.requires_native
def test_native_packet_mixed_radix_sparse_avoids_machine_overflow():
    nr=pytest.importorskip('native_recursive')
    R=Padic(5,modulus_polynomial(5),13)
    assert nr.packet_evaluate((),R,(),(),(),(2**90,),(),())==R.zero
    assert nr.packet_evaluate((),R,(),(),(),(),(),())==R.one


@pytest.mark.requires_native
def test_native_leaf_matches_random_reference_exactly():
    nr=pytest.importorskip('native_recursive')
    rng=random.Random(455)
    R=Padic(5,modulus_polynomial(5),13)
    for n in range(1,5):
        for _ in range(5):
            tab1={bits:rng.randint(0,2) for bits in product((0,1),repeat=n)}
            tab2={bits:rng.randint(0,2) for bits in product((0,1),repeat=n)}
            net=simple_network(n,[(tuple(range(n)),tab1)],[(tuple(range(n)),tab2)])
            expect=eliminate_leaf(net,R,10)
            assert nr.eliminate_leaf(net,R,10)==expect
            assert expect==net.direct(R,10)


def test_capacity_refusal_under_optional_kernels():
    from non_exponential_sudoku.runtime.budget import CapacityError
    net=simple_network(2,[((0,1), {(0,0):1})],[((0,1), {(0,0):1})])
    for cfg in (RecursionConfig(),RecursionConfig(child_plans=True,native_leaf=True,native_packet=True,
                                                 packet_memo_entries=128)):
      e=ContractionEngine(ContractorConfig(2,5,schedule='micro',
          recovery=RecoveryConfig(method='jet',max_jet_coordinates=20),
          micro_active_depth=2,recursion=cfg))
      with pytest.raises(CapacityError,match='Nested jet needs'):
        e.contract(net)


def test_explicit_complete_exhaustive_fallback_and_bound():
    # No capacity guard; this is a 2**M baseline, not Appendix-D recurrence.
    net=simple_network(4,[([i],{(0,):1,(1,):1}) for i in range(4)],
                         [([i],{(0,):1,(1,):1}) for i in range(4)])
    c=ContractionEngine(ContractorConfig(4,9,schedule='paper',leaf=LeafConfig(limit=1)))
    assert c.contract_complete(net)[0]==16
    with pytest.raises(CapacityError):
        c.contract(net)


def test_bounded_child_plans_default_matches_explicit_reference():
    """The optimized default must preserve exact counts and recursion shape."""
    assert RecursionConfig().child_plans
    for case_id in ('nested-2wire', 'sudoku-4wire'):
        reference = get_case(case_id, 'reference')
        expected, baseline_stats = reference.validate()
        optimized = replace(reference.config, recursion=RecursionConfig())
        engine = ContractionEngine(optimized)
        assert engine.contract(reference.network)[0] == expected
        assert engine.stats.recursive_calls == baseline_stats.recursive_calls
        assert engine.stats.child_networks == baseline_stats.child_networks
        assert engine.stats.child_plan_cache_hits > 0


def test_compiled_child_refuses_mismatched_multiplicity_lengths() -> None:
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    ring = Padic(5, modulus_polynomial(5), 13)
    modes = mode_catalog(net, packing, 1, ring.p)
    plan = CompiledChildPlan(net, packing, 0, 0)
    context = EvaluationContext(1, ring.one, ring, 1,
                                prepared_packet_entries=16)
    for bad_beta in ((0,) * (len(modes) - 1), (0,) * (len(modes) + 1)):
        with pytest.raises(ValueError, match='one multiplicity per mode'):
            plan.instantiate(modes, bad_beta, 1, ring.one, ring, context)
    assert context.prepared_packets is not None
    assert context.prepared_packets.misses == 0


def test_workspaces_release_network_after_success_and_refusal(monkeypatch) -> None:
    from non_exponential_sudoku.contraction.workspaces import FrameWorkspace

    case = get_case('nested-2wire', 'plans')
    engine = ContractionEngine(case.config)
    assert engine.contract(case.network)[0] == case.expected
    assert engine._frames == {}
    assert engine._active_contract_calls == 0

    def fail_plan(*args: object, **kwargs: object) -> object:
        raise RuntimeError('deliberate child construction failure')

    with monkeypatch.context() as context:
        context.setattr(FrameWorkspace, 'get_plan', fail_plan)
        with pytest.raises(RuntimeError, match='deliberate child'):
            engine.contract(case.network)
    assert engine._frames == {}
    assert engine._active_contract_calls == 0
    assert engine.contract(case.network)[0] == case.expected
    assert engine._frames == {}


def test_reference_packet_terms_also_refuse_truncated_modes() -> None:
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    ring = Padic(5, modulus_polynomial(5), 13)
    modes = mode_catalog(net, packing, 1, ring.p)
    context = EvaluationContext(1, ring.one, ring, 1)
    with pytest.raises(ValueError, match='one multiplicity per mode'):
        make_child(net, packing, modes, (0,) * (len(modes) - 1),
                   1, ring.one, ring, 0, 0, context)


def test_children_keep_source_labels_and_compiled_packet_labels() -> None:
    net = port_graph_with_cross_mode()
    packing = pack(net, 2, 1, (((0,),), ((1,),)))
    ring = Padic(5, modulus_polynomial(5), 9)
    modes = mode_catalog(net, packing, 1, ring.p)
    beta = (0,) * len(modes)
    context = EvaluationContext(1, ring.one, ring, packing.a)
    direct = make_child(net, packing, modes, beta, 1, ring.one, ring,
                        0, 0, context)
    plan = CompiledChildPlan(net, packing, 0, 0)
    compiled = plan.instantiate(modes, beta, 1, ring.one, ring, context)
    parent_names = {vertex.name for vertex in net.left + net.right}
    assert [vertex.name for vertex in direct.left] == [
        vertex.name for vertex in compiled.left]
    assert all(vertex.name in parent_names for vertex in direct.left)
    assert [vertex.name for vertex in compiled.right] == [
        spec.name for spec in plan.packet_ports]
    assert [vertex.name for vertex in direct.right] == [
        vertex.name for vertex in compiled.right]
    # A second compilation uses the original name, not a growing keep: prefix.
    next_packing = pack(compiled, 2, 1)
    next_plan = CompiledChildPlan(compiled, next_packing, 0, 0)
    assert all(vertex.name in {v.name for v in compiled.left + compiled.right}
               for vertex in next_plan.kept)
