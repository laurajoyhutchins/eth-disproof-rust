"""Reproducible exact recursive benchmark cases and kernel configurations.

The case label is shared by pytest-benchmark, the correctness JUnit gate,
and fresh subprocess RSS/allocation measurements. No timing occurs here.
"""
from __future__ import annotations
from dataclasses import dataclass,replace
from non_exponential_sudoku import (
    ContractionEngine,ContractorConfig,ModeConfig,LeafConfig,RecoveryConfig,
    RecursionConfig,ZeroSupportPolicy,Padic,Network,simple_network
)
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.core.modes import mode_catalog
from reference.scaling_experiment import parity_network
from reference.local_support import pin_band_wires
from reference.real_sudoku_bench import puzzles

VARIANTS={
    'reference':RecursionConfig(child_plans=False),
    'plans':RecursionConfig(child_plans=True),
    'certified-zero':RecursionConfig(child_plans=True,
        zero_support=ZeroSupportPolicy(enabled=True)),
    'packet':RecursionConfig(child_plans=False,native_packet=True),
    'leaf':RecursionConfig(child_plans=False,native_leaf=True),
    'combined':RecursionConfig(child_plans=True,native_packet=True,native_leaf=True),
    'memo':RecursionConfig(child_plans=False,packet_memo_entries=128),
    'memo-all':RecursionConfig(child_plans=True,native_packet=True,native_leaf=True,packet_memo_entries=128),
}
IDS=('parity-2wire','sudoku-4wire','sudoku-8wire','nested-2wire','crossing-4wire')
EXPECTED={'parity-2wire':2,'sudoku-4wire':2,'sudoku-8wire':4,'nested-2wire':4,
          'crossing-4wire':16}


@dataclass(frozen=True)
class RecursiveCase:
    case_id: str
    variant: str
    expected: int
    parameters: dict
    network: Network
    config: ContractorConfig
    deformation_only: bool=False

    def run(self):
        engine=ContractionEngine(self.config)
        if self.deformation_only:
            pk=pack(self.network,64,2,
                (tuple((0,0) for _ in range(4)),tuple((1,0) for _ in range(4))))
            R=Padic(engine.e,engine.f,9)
            modes=mode_catalog(self.network,pk,1,9)
            answer=engine.evaluate_deformation(self.network,pk,modes,1,R.basis(3),R,0)[0]
        else:
            answer=engine.contract(self.network)[0]
        return answer,engine.stats

    def validate(self):
        got,stats=self.run()
        if got!=self.expected:
            raise AssertionError(f'{self.case_id}/{self.variant}: expected {self.expected}, got {got}')
        return got,stats


def get_case(case_id: str, variant: str) -> RecursiveCase:
    if case_id not in IDS or variant not in VARIANTS:
        raise ValueError('Unknown recursive benchmark case or variant')
    cfg=VARIANTS[variant]
    if case_id=='parity-2wire':
        net=parity_network('cycle2',1)
    elif case_id.startswith('sudoku-'):
        label=('9x9-77-givens-two-solutions' if case_id=='sudoku-4wire'
               else '9x9-73-givens-four-solutions')
        puzzle=next(p for name,p,_ in puzzles() if name==label)
        net,_=pin_band_wires(puzzle)
    elif case_id=='nested-2wire':
        tab={(a,b):1 for a in (0,1) for b in (0,1)}
        net=simple_network(2,[([0,1],tab)],[([0,1],tab)])
    else:
        net=simple_network(4,[([i],{(0,):1,(1,):1}) for i in range(4)],
                               [([i],{(0,):1,(1,):1}) for i in range(4)])
    if case_id=='crossing-4wire':
        config=ContractorConfig(4,9,schedule='geometry64',
              leaf=LeafConfig(strategy='eliminate'),recursion=cfg)
    else:
        config=ContractorConfig(net.edges,net.edges+3,schedule='micro',
              leaf=LeafConfig(strategy='eliminate'),
              recovery=RecoveryConfig(method='jet',streaming=True),
              mode=ModeConfig(strategy='eliminate',factorization='components',join='adaptive'),
              root_labels=(((0,),),((1,),)) if case_id=='nested-2wire' else None,
              micro_active_depth=2 if case_id=='nested-2wire' else 1,
              recursion=cfg)
    return RecursiveCase(case_id,variant,EXPECTED[case_id],{
        'family':case_id,'wires':net.edges,'variant':variant,
        'recursive_active_depth':2 if case_id=='nested-2wire' else 1,
        'packet_memo_entries':cfg.packet_memo_entries,
        'jit_packet':cfg.native_packet,'jit_leaf':cfg.native_leaf,
        'compiled_child_plans':cfg.child_plans},net,config,
        deformation_only=case_id=='crossing-4wire')
