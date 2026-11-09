"""Opt-in mathematical assumptions stay separate from green software tests."""
from __future__ import annotations

from dataclasses import replace
from math import isqrt

import pytest

from non_exponential_sudoku.runtime.config import ContractorConfig, ModeConfig
from reference.precision_envelope import paper_frame_envelopes
from reference.whole_frame_recurrence import (
    OPEN_PREMISES,
    UnclosedRecurrence,
    assemble_paper_recurrence,
    ceil_log2,
    log2_sum_ceiling,
    numeric_fallback_leaf_edge_ceiling,
)

pytestmark = pytest.mark.checkpoint


def _paper(lam: int = 131072) -> tuple[ContractorConfig, int]:
    s = (1 << (lam - 1)) + 1
    return (ContractorConfig(
        s=s, precision=33, schedule='paper',
        mode=ModeConfig(native_sparse=False),
    ), s)


def test_log_sum_is_an_integer_upper_bound() -> None:
    for a in range(6):
        for b in range(6):
            assert (1 << a) + (1 << b) <= (1 << log2_sum_ceiling(a, b))
            assert max(a, b) <= log2_sum_ceiling(a, b)
    for bad in (0, -1, 1.5):
        with pytest.raises(ValueError):
            ceil_log2(bad)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        log2_sum_ceiling()
    with pytest.raises(ValueError):
        log2_sum_ceiling(1, -1)


@pytest.mark.parametrize('lam', [131072, 262144, 524288])
def test_complete_recurrence_frame_shape_matches_independent_schedule(lam: int) -> None:
    cfg, s = _paper(lam)
    bound = assemble_paper_recurrence(cfg, edges=s, vertices=s,
                                      input_name_bits=128)
    actual = paper_frame_envelopes(cfg, s, s)
    assert len(bound.frames) == len(actual)
    assert bound.frames[-1].terminal
    assert all(not f.terminal for f in bound.frames[:-1])
    assert [f.depth for f in bound.frames] == [f.depth for f in actual]
    for frame in bound.frames[:-1]:
        assert frame.center_count_ceiling == actual[frame.depth].centers
        assert frame.sample_count_ceiling == actual[frame.depth].evaluations_per_center
        assert frame.log2_child_calls_ceiling > 0
        assert frame.log2_named_local_work_ceiling >= max(
            frame.log2_factor_ring_bit_work_ceiling,
            frame.log2_child_preparation_bit_work_ceiling,
            frame.log2_newton_interpolation_bit_work_ceiling,
            frame.log2_rational_recovery_bit_work_ceiling,
        )
    assert bound.log2_path_fanout_ceiling == sum(
        f.log2_child_calls_ceiling for f in bound.frames[:-1]
    )
    # This is a consequence of the exact charged terms, NOT a certificate
    # that the remaining source operations are polynomial or non-refusing.
    assert bound.hypothetical_polynomial_glue_log2_bound(degree=3) >= (
        bound.log2_recursive_calls_ceiling
    )


def test_weighted_support_replaces_default_refusal_cap() -> None:
    cfg, s = _paper()
    result = assemble_paper_recurrence(cfg, edges=s, vertices=s,
                                       input_name_bits=128)
    assert result.frames[0].log2_child_calls_ceiling > ceil_log2(
        cfg.limits.max_child_contractions
    )
    assert result.frames[0].log2_weighted_support_ceiling > 0
    # A theorem must not pretend that exceeding a configured runtime cap
    # has caused expensive assignments to disappear.
    assert result.frames[0].log2_child_calls_ceiling > (
        result.frames[0].log2_weighted_support_ceiling
    )


def test_failed_premises_never_become_free_operations() -> None:
    cfg, s = _paper()
    result = assemble_paper_recurrence(cfg, edges=s, vertices=s,
                                       input_name_bits=128)
    assert OPEN_PREMISES == result.open_premises
    with pytest.raises(UnclosedRecurrence, match='input_oracle_bit_contract'):
        result.require_complete_theorem()
    with pytest.raises(UnclosedRecurrence, match='resource_limits'):
        result.require_complete_theorem()
    with pytest.raises(ValueError):
        result.hypothetical_polynomial_glue_log2_bound(degree=0)
    assert (result.hypothetical_polynomial_glue_log2_bound(degree=10)
            >= result.hypothetical_polynomial_glue_log2_bound(degree=2))


def test_default_native_sparse_policy_cannot_claim_python_reference_proof() -> None:
    cfg, s = _paper()
    default = replace(cfg, mode=ModeConfig())
    with pytest.raises(UnclosedRecurrence, match='Python elimination'):
        assemble_paper_recurrence(default, edges=s, vertices=s,
                                   input_name_bits=128)
    with pytest.raises(UnclosedRecurrence, match='Python elimination'):
        assemble_paper_recurrence(replace(cfg, schedule='micro'), edges=s,
                                   vertices=s, input_name_bits=128)


@pytest.mark.parametrize('kind', ['edges', 'precision', 'vertices', 'names'])
def test_refuses_unbounded_explicit_input_size(kind: str) -> None:
    cfg, s = _paper()
    edges, vertices, names = s, s, 128
    if kind == 'edges':
        edges = s + 1
    if kind == 'vertices':
        vertices = s*s + 1
    if kind == 'names':
        names = s*s + 1
    if kind == 'precision':
        cfg = replace(cfg, precision=s+1)
    with pytest.raises(UnclosedRecurrence, match='polynomial input shape'):
        assemble_paper_recurrence(cfg, edges=edges, vertices=vertices,
                                   input_name_bits=names)


def test_terminal_paper_frame_charges_exponential_leaf_assignments() -> None:
    # The present code refuses a large leaf at its fixed cap; counting its
    # potentially exponential reference work does NOT make that refusal OK.
    cfg = ContractorConfig(s=96, precision=33, schedule='paper',
                           mode=ModeConfig(native_sparse=False))
    result = assemble_paper_recurrence(cfg, edges=96, vertices=28,
                                       input_name_bits=32)
    assert len(result.frames) == 1 and result.frames[0].terminal
    assert result.frames[0].log2_exhaustive_leaf_assignments == 96
    assert result.early_numeric_fallback_leaf_edge_ceiling == 96
    with pytest.raises(UnclosedRecurrence):
        result.require_complete_theorem()


def test_numeric_exception_fallback_not_omitted() -> None:
    cfg, s = _paper()
    result = assemble_paper_recurrence(cfg, edges=s, vertices=s,
                                       input_name_bits=128)
    lam = max(1, (s - 1).bit_length())
    a = result.frames[0].center_count_ceiling.bit_length() - 1
    # L=(centers+1)/2, hence a = log2((centers+1)/2).
    actual_a = ((result.frames[0].center_count_ceiling + 1)//2).bit_length()-1
    assert a >= actual_a
    fallback = numeric_fallback_leaf_edge_ceiling(
        s=s, lambda_bits=lam, maximum_slot_exponent=actual_a,
        terminal_edges=result.frames[-1].edges,
    )
    assert fallback == result.early_numeric_fallback_leaf_edge_ceiling
    assert fallback >= result.frames[-1].edges
    assert fallback >= (s + isqrt(lam)-1)//isqrt(lam)
    assert 0 < fallback < s  # for this symbolic, very large fixed size
    with pytest.raises(ValueError):
        numeric_fallback_leaf_edge_ceiling(
            s=s, lambda_bits=3, maximum_slot_exponent=2,
            terminal_edges=result.frames[-1].edges,
        )


def test_multiple_active_depths_multiply_not_add_child_fanout() -> None:
    cfg, s = _paper(262144)
    result = assemble_paper_recurrence(cfg, edges=s, vertices=s,
                                       input_name_bits=128)
    assert len(result.frames) >= 3
    logs = [f.log2_child_calls_ceiling for f in result.frames[:-1]]
    assert result.log2_path_fanout_ceiling == sum(logs)
    assert result.log2_recursive_calls_ceiling >= max(logs)
    assert result.log2_recursive_calls_ceiling > min(logs)


def test_hypothetical_closure_is_not_a_theorem_and_no_silent_green() -> None:
    cfg, s = _paper()
    result = assemble_paper_recurrence(cfg, edges=s, vertices=s,
                                       input_name_bits=128)
    trial = result.hypothetical_polynomial_glue_log2_bound(degree=6)
    assert trial >= result.frames[0].log2_named_local_work_ceiling
    with pytest.raises(UnclosedRecurrence):
        result.require_complete_theorem()

def test_packing_and_ordering_source_cost_is_charged_but_not_theorem_proved() -> None:
    cfg, s = _paper()
    recurrence = assemble_paper_recurrence(
        cfg, edges=s, vertices=s, input_name_bits=128,
    )
    for f in recurrence.frames[:-1]:
        assert f.log2_packing_ordering_bit_work_ceiling > 0
        assert f.log2_named_local_work_ceiling >= f.log2_packing_ordering_bit_work_ceiling
    # A well-formed partial cost receipt cannot certify packing lemma
    # correctness, callback totality, memory, or cell-based asymptotics.
    with pytest.raises(UnclosedRecurrence, match='packing_planning'):
        recurrence.require_complete_theorem()
