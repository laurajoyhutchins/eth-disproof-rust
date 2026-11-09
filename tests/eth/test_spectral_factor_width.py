"""Independently verify group interaction scopes of the paper's auxiliary.

These fixtures use exact swap/spectral interpolation and real
incidence-to-coordinate transfer, not a manually selected measurement
design. Their finite n does not satisfy literal main-body admission.
"""
from __future__ import annotations

from fractions import Fraction

import pytest

from benchmarks.eth.spectral_factor_width_probe import ring_formula
from non_exponential_sudoku.eth import (
    CNFFormula, construct_bounded_designs, construct_from_schedules,
    construct_implicit_auxiliary, choose_balanced_schedules,
)
from non_exponential_sudoku.eth.design import certify_measurements
from non_exponential_sudoku.eth.factor_width import audit_factor_width

@pytest.mark.integration
@pytest.mark.parametrize('r,Q,R,n,width', [
    (2, 2, 2, 6, 2),
    (3, 2, 2, 6, 2),
])
def test_spectral_scopes_are_exact_nonzero_cross_group_coefficients(
    r: int, Q: int, R: int, n: int, width: int,
) -> None:
    formula = ring_formula(n, width=width)  # type: ignore[arg-type]
    constructed = construct_bounded_designs(
        formula, r=r, Q=Q, R=R, schedule='conditional',
        representation='implicit', measurement_basis='projector')
    assert constructed.balancing is not None
    assert constructed.balancing.final_potential <= constructed.balancing.initial_potential
    assert constructed.paper_admission is not None
    assert not constructed.paper_admission.admitted
    for center, design in constructed.centers:
        certificate = certify_measurements(
            formula, constructed.replacements, design, at=center)
        audit = audit_factor_width(certificate)
        assert audit.measurement_rows == sum(map(len, design.matrices))
        for owner, forms, actual in zip(
            design.clause_groups, constructed.replacements.clauses,
            audit.factor_scopes,
        ):
            external = {
                group for group, variables in enumerate(design.groups)
                if group != owner and any(
                    form.coefficients[v].evaluate(center) != 0
                    for form in forms for v in variables)
            }
            assert actual == tuple(sorted({owner} | external))
        assert audit.max_scope_groups <= r
        assert audit.max_domain_bits <= n


@pytest.mark.integration
def test_projected_and_selector_measurement_bases_induce_same_scopes() -> None:
    formula = CNFFormula(6, tuple(
        (i + 1, (i + 1) % 6 + 1) for i in range(6)))
    schedules = choose_balanced_schedules(formula, r=3, Q=2)
    a, d = schedules.variable_schedules, schedules.clause_schedules
    bases = (
        construct_implicit_auxiliary(
            r=3, Q=2, R=2, measurement_basis='selectors'),
        construct_implicit_auxiliary(
            r=3, Q=2, R=2, measurement_basis='projector'),
    )
    constructions = [
        construct_from_schedules(formula, basis, a, d)
        for basis in bases
    ]
    assert constructions[0].replacements == constructions[1].replacements
    for (center, old), (same_center, compressed) in zip(
        constructions[0].centers, constructions[1].centers
    ):
        assert center == same_center
        old_audit = audit_factor_width(certify_measurements(
            formula, constructions[0].replacements, old, at=center))
        new_audit = audit_factor_width(certify_measurements(
            formula, constructions[1].replacements, compressed, at=center))
        assert old_audit.factor_scopes == new_audit.factor_scopes
        assert old_audit.interaction_edges == new_audit.interaction_edges
        assert old_audit.max_scope_groups == new_audit.max_scope_groups
        assert old_audit.max_domain_bits == new_audit.max_domain_bits
        # Measurements are a representation choice; dependent directions
        # can be reduced, but not removed when the cross vector is nonzero.
        assert new_audit.measurement_rows <= old_audit.measurement_rows


@pytest.mark.integration
def test_spectral_width_probe_preserves_admission_as_independent_claim() -> None:
    formula = CNFFormula(3, ((1, 2), (-1, 3)))
    constructed = construct_bounded_designs(
        formula, r=2, Q=2, R=2,
        schedule='conditional', measurement_basis='projector')
    assert constructed.paper_admission is not None
    assert not constructed.paper_admission.admitted
    # The manually chosen auxiliary r=2 is not the paper's n-derived r=1.
    assert constructed.auxiliary.r == 2
    assert constructed.paper_admission.parameters.r == 1
    assert 'r_at_least_two' in constructed.paper_admission.failures
