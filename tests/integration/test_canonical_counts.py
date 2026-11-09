"""Canonical independently counted Sudoku contract cases."""
import pytest
from non_exponential_sudoku import (
    ContractionEngine,ContractorConfig,LeafConfig,RecoveryConfig,ModeConfig,
)
from reference.real_sudoku_bench import puzzles,independent_count_sparse
from reference.local_support import pin_band_wires
from tests.fixtures.cases import SUDOKU_CASES

pytestmark=pytest.mark.integration


@pytest.mark.parametrize('case', SUDOKU_CASES, ids=lambda case:case.id)
def test_canonical_sudoku_case(case):
    name,puzzle,expect=next(p for p in puzzles() if p[0]==case.id)
    assert expect==case.expected
    assert independent_count_sparse(puzzle,12)==case.expected
    net,_=pin_band_wires(puzzle)
    assert net.edges==case.parameter
    engine=ContractionEngine(ContractorConfig(
        net.edges,net.edges+3,schedule='micro',
        leaf=LeafConfig(strategy='eliminate'),
        recovery=RecoveryConfig(method='jet',streaming=True),
        mode=ModeConfig(factorization='components',join='adaptive')))
    result=engine.contract(net)
    assert result[0]==case.expected
