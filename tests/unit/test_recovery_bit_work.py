"""Independent correctness and work-envelope checks for rational recovery."""
from __future__ import annotations

from collections import Counter
from collections.abc import Callable
from fractions import Fraction
from math import comb

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial, v2
from non_exponential_sudoku.contraction.engine import paper_schedule_parameters
from non_exponential_sudoku.recovery.streaming import StreamingHermite
from non_exponential_sudoku.runtime.config import ContractorConfig
from reference.precision_envelope import paper_frame_envelopes
from reference.recovery_bit_work import recovery_work

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize('M,L,u', [(0,2,1),(1,2,1),(2,4,1),(2,4,3),
                                    (1,4,4),(3,8,1),(3,8,3)])
def test_valuation_class_counts_match_literal_schedule(M:int,L:int,u:int)->None:
    e=recovery_work(M,L,u,7,extension_degree=3)
    a=L.bit_length()-1
    h=(3*M+u-1)//u
    qs={t:h*max(0,u-v2(t)) for t in range(-L,L) if t}
    active=[t for t in qs if qs[t]]
    assert e.centers==len(active)
    assert e.coefficients==sum(qs.values())
    assert e.max_order==max(qs.values(),default=0)
    assert e.center_scans==len(qs)*len(active)
    assert e.normalize_pairs==len(active)*max(0,len(active)-1)
    assert e.max_center_precision==max(
        (7+8*h*(L//(1<<v2(t)))+8*M*(a+1) for t in active),default=7)


@pytest.mark.parametrize('M,L,u',[(1,2,1),(2,4,1),(2,2,2)])
def test_real_recovery_and_outer_ring_dispatch_bounds(
    M:int,L:int,u:int,monkeypatch:pytest.MonkeyPatch,
)->None:
    p=9
    R=Padic(3,modulus_polynomial(3),p)
    recovery=StreamingHermite(M,L,u,R)
    evidence=recovery_work(M,L,u,p,extension_degree=3)
    polynomial=(3,-2,1)
    jets={}
    for t,q in recovery.qs.items():
        if not q:continue
        elevated=Padic(R.e,R.f,recovery.precision(t))
        jets[t]=[
            elevated.scalar(sum(polynomial[k]*comb(k,j)*recovery.alpha**j*t**(k-j)
                                for k in range(j,len(polynomial))))
            for j in range(q)
        ]
    names=('add','mul','neg','pow','rational','scalar')
    originals={name:getattr(Padic,name) for name in names}
    counter:Counter[str]=Counter()
    depth=[0]
    for name in names:
        original=originals[name]
        def wrap(label:str,f:Callable[...,object])->Callable[...,object]:
            def traced(self:Padic,*args:object)->object:
                if depth[0]==0: counter[label]+=1
                depth[0]+=1
                try: return f(self,*args)
                finally: depth[0]-=1
            return traced
        monkeypatch.setattr(Padic,name,wrap(name,original))
    for t,jet in jets.items():
        recovery.add_center(t,jet)
    assert recovery.finish()[0]==3
    assert recovery.centers==evidence.centers
    assert counter['add']<=evidence.ring_additions
    assert counter['mul']<=evidence.ring_multiplies
    assert counter['neg']<=evidence.ring_negations
    assert counter['pow']<=evidence.ring_powers
    assert counter['scalar']<=evidence.binomial_calls
    assert counter['rational']<=evidence.normalize_pairs+evidence.coordinates


@pytest.mark.parametrize('M,L,u',[(1,2,1),(2,4,1),(3,4,2),(2,8,1)])
def test_independent_fraction_prefix_widths_stay_bounded(M:int,L:int,u:int)->None:
    p=7
    env=recovery_work(M,L,u,p,extension_degree=3)
    a=L.bit_length()-1
    h=(3*M+u-1)//u
    qs={t:h*max(0,u-v2(t)) for t in range(-L,L) if t}
    accumulator=Fraction(0)
    n=0
    for t,q in qs.items():
        if not q:continue
        normal=Fraction(1)
        for other,m in qs.items():
            if other==t or m==0:continue
            normal *= Fraction(-other,t-other)**m
            assert abs(normal.numerator).bit_length() <= env.max_scale_bits
            assert normal.denominator.bit_length() <= env.max_scale_bits
        pt=p+8*h*(L//(1<<v2(t)))+8*M*(a+1)
        for j in range(q):
            scale=normal*Fraction(-t,2*L)**j
            assert abs(scale.numerator).bit_length()<=env.max_scale_bits
            assert scale.denominator.bit_length()<=env.max_scale_bits
            accumulator+=scale*((1<<pt)-1)
            n+=1
            assert abs(accumulator.numerator).bit_length()<=env.max_answer_numerator_bits
            assert accumulator.denominator.bit_length()<=env.max_answer_denominator_bits
    assert n==env.coefficients


def test_symbolic_paper_precision_and_polynomial_bit_model() -> None:
    for lam in (131072,262144,524288):
        s=(1<<(lam-1))+1
        cfg=ContractorConfig(s=s,precision=33,schedule='paper')
        for frame in paper_frame_envelopes(cfg,edges=s,vertices=s):
            if frame.terminal:continue
            _,a,u,_=paper_schedule_parameters(s,lam,frame.depth)
            result=recovery_work(frame.edges,1<<a,u,frame.precision,
                                 extension_degree=4*lam)
            assert result.max_center_precision==frame.child_precision
            assert result.coefficients>0
            # Finite regression of formulas; the polynomial conclusion
            # follows from inequalities in the proof note, not this sample.
            assert result.max_rational_bits.bit_length()<10*lam
            assert result.schoolbook_bit_work_majorant(4*lam).bit_length()<50*lam


def test_invalid_inputs_refuse_and_memory_is_not_claimed_to_be_rss()->None:
    for M,L,u,p in ((1,3,1,8),(1,4,0,8),(-1,4,1,8),(1,4,1,0)):
        with pytest.raises(ValueError):recovery_work(M,L,u,p,extension_degree=3)
    with pytest.raises(ValueError):recovery_work(1,2,1,8,extension_degree=1)
    with pytest.raises(ValueError):
        recovery_work(1,2,1,8,extension_degree=3,inherited_jet_lengths=(0,))
    nested=recovery_work(2,4,1,13,extension_degree=5,inherited_jet_lengths=(2,3))
    assert nested.coordinates==30
    assert nested.eager_input_payload_bits>=nested.center_payload_bits
    assert nested.retained_abstract_payload_bits>=nested.center_payload_bits
