"""A contracting network is exactly its directly enumerated tensor sum."""
import pytest
from non_exponential_sudoku import ContractionEngine, ContractorConfig
from non_exponential_sudoku.core.network import simple_network

pytestmark = pytest.mark.checkpoint


def test_single_edge_matches_independent_truth_table() -> None:
    left = {(0,): 1, (1,): 2}
    right = {(0,): 3, (1,): 5}
    net = simple_network(1, [([0], left)], [([0], right)])
    expected = sum(left[(bit,)] * right[(bit,)] for bit in (0, 1))
    contractor = ContractionEngine(ContractorConfig(
        1, 4, schedule='micro', root_labels=(((0,),), ((1,),)),
    ))
    assert contractor.contract(net)[0] == expected == 13
