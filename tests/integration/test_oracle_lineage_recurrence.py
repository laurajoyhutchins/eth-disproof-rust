"""Deep symbolic paper-model lineage check, outside the fast checkpoint tier."""
from __future__ import annotations

import pytest

from non_exponential_sudoku.runtime.config import ContractorConfig, ModeConfig
from reference.oracle_lineage import paper_single_path_descriptor_bound
from reference.whole_frame_recurrence import assemble_paper_recurrence, UnclosedRecurrence

pytestmark = pytest.mark.integration


def test_inherited_packet_name_budget_is_included_in_whole_frame_cost() -> None:
    lam = 131072
    scale = (1 << (lam - 1)) + 1
    cfg = ContractorConfig(s=scale, precision=33, schedule="paper",
                           mode=ModeConfig(native_sparse=False))
    root_edges, root_vertices, root_names = scale, scale, 80
    bound = paper_single_path_descriptor_bound(
        root_edges=root_edges, root_vertices=root_vertices,
        root_input_name_bits=root_names,
    )
    model = assemble_paper_recurrence(
        cfg, edges=root_edges, vertices=root_vertices,
        input_name_bits=root_names,
    )
    assert model.max_single_path_oracle_descriptors == bound.max_vertices
    assert model.max_single_path_oracle_name_bits == bound.max_visible_name_bits
    assert model.max_single_path_oracle_name_bits > root_names
    assert all(frame.vertices <= bound.max_vertices for frame in model.frames)
    assert 'input_oracle_bit_contract_and_uniform_metadata' in model.open_premises
    with pytest.raises(UnclosedRecurrence):
        model.require_complete_theorem()
