"""Certified counterexample to inferring group width from measurement count.

The certificate, occurrence bound, clause width, group sizes and measured
L1 are all checked.  The literal paper n-derived r,Q,R construction is
NOT invoked or claimed.
"""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction
from itertools import combinations

import pytest

from benchmarks.eth.factor_width_obstruction import (
    build_clique_witness, certified_witness_profile,
)
from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
from non_exponential_sudoku.eth.design import (
    MeasurementDesign, certify_measurements,
)
from non_exponential_sudoku.eth.factor_width import audit_factor_width
from non_exponential_sudoku.eth.interpolation import count_origin_from_manual_designs
from non_exponential_sudoku.eth.polynomial import ReplacementSystem
from non_exponential_sudoku.eth.taylor import TaylorLimits
from non_exponential_sudoku.runtime.budget import CapacityError


@pytest.mark.checkpoint
@pytest.mark.parametrize('r', [3, 4])
def test_certified_clique_has_exact_induced_width(r: int) -> None:
    witness = build_clique_witness(r, r - 1)
    formula, design = witness.formula, witness.design
    identity = ReplacementSystem.identity(formula)
    assert count_bruteforce(formula) == r + 1
    for center in (Fraction(1), Fraction(2)):
        certificate = certify_measurements(formula, identity, design, at=center)
        audit = audit_factor_width(certificate)
        assert audit.measurement_rows == r * (r - 1)
        assert audit.interaction_edges == tuple(combinations(range(r), 2))
        assert audit.complete_graph
        assert audit.exact_treewidth_if_complete == r - 1
        assert audit.max_scope_groups == r
        assert audit.max_domain_bits == formula.nvars
        # Every original clause still depends on at most two groups.
        assert all(len(scope) <= 2 for scope in audit.factor_scopes)
        assert len(audit.elimination_order) == r
        assert all(len(row) == len(design.groups[g])
                   for g, matrix in enumerate(design.matrices)
                   for row in matrix)
    result = count_origin_from_manual_designs(
        formula, ((Fraction(1), design),), order=0, summation='eliminate')
    assert result.count == r + 1
    assert result.taylor_data[0].stats.factor_scope_peak == r


@pytest.mark.checkpoint
def test_missing_boundary_measurement_invalidates_certificate() -> None:
    witness = build_clique_witness(3, 2)
    # The largest group is referenced by BOTH lower-index owners.  Removing
    # its first boundary direction must invalidate the cross-group witness.
    matrices = (*witness.design.matrices[:2], witness.design.matrices[2][1:])
    corrupted = replace(witness.design, matrices=matrices)
    with pytest.raises(ValueError, match='row space'):
        certify_measurements(
            witness.formula, ReplacementSystem.identity(witness.formula),
            corrupted, at=1,
        )


@pytest.mark.checkpoint
def test_width_analysis_handles_noncomplete_graph_and_forced_masks() -> None:
    formula = CNFFormula(3, ((1, 2), (2, 3)))
    design = MeasurementDesign(
        groups=((0,), (1,), (2,)), clause_groups=(0, 1),
        matrices=(((1,),), ((1,),), ((1,),)),
        tau=Fraction(1, 2), D=1,
    )
    certificate = certify_measurements(
        formula, ReplacementSystem.identity(formula), design, at=1)
    audit = audit_factor_width(certificate)
    assert not audit.complete_graph
    assert audit.exact_treewidth_if_complete is None
    assert audit.interaction_edges == ((0, 1), (1, 2))
    assert audit.max_scope_groups == 2
    assert audit.max_domain_bits == 2
    forced = audit_factor_width(certificate, forced=(1,))
    assert forced.max_domain_bits == 1
    assert forced.max_scope_groups == 2
    with pytest.raises(ValueError, match='sorted'):
        audit_factor_width(certificate, forced=(2, 0))
    with pytest.raises(ValueError, match='outside'):
        audit_factor_width(certificate, forced=(3,))


@pytest.mark.integration
@pytest.mark.parametrize('r,size', [(3, 22), (4, 48)])
def test_low_tau_bounded_occurrence_still_has_clique_width(
    r: int, size: int,
) -> None:
    profile = certified_witness_profile(r, size)
    assert profile['nvars'] == r * size
    assert profile['measurement_rows'] == r * (r - 1)
    assert profile['measurement_D'] == 1
    assert profile['max_occurrences'] == 3
    assert profile['max_clause_width'] <= 3
    assert profile['tau_bound_met']
    assert profile['complete_group_graph']
    assert profile['graph_edges'] == r * (r - 1) // 2
    assert profile['exact_group_treewidth'] == r - 1
    assert profile['max_induced_scope_groups'] == r
    assert profile['log2_largest_dense_factor_domain'] == r * size
    assert profile['paper_parameter_schedule_admitted'] is False


@pytest.mark.integration
def test_large_clique_witness_refuses_factor_domain_without_enumerating() -> None:
    witness = build_clique_witness(3, 22)
    with pytest.raises(CapacityError, match='factor work'):
        count_origin_from_manual_designs(
            witness.formula, ((Fraction(1), witness.design),), order=0,
            summation='eliminate',
            taylor_limits=TaylorLimits(max_factor_work=1_000),
        )
