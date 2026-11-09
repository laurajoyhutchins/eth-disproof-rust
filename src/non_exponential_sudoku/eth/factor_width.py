"""Structural width audit of certified ETH group-factor summation.

A small number of measurement rows does not imply a sparse interaction
graph: the same measurement coordinate can be reused by many clauses.
This audit uses *certified* nonzero lambda coefficients, not raw CNF
incidence, and predicts the domains of a min-domain elimination schedule.

Its domain exponents are upper bounds on dense table *possibilities*,
not lower bounds on all possible algebraic or sparse algorithms.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations

from .design import MeasurementCertificate


@dataclass(frozen=True, slots=True)
class FactorWidthAudit:
    """Reproducible graph structure and domain-size estimates.

    max_domain_bits is the base-2 logarithm of the largest domain
    of a *formed or joined* group factor, not an observed memory cost.
    complete_graph implies exact structural treewidth = groups - 1.
    """

    groups: int
    factors: int
    measurement_rows: int
    factor_scopes: tuple[tuple[int, ...], ...]
    interaction_edges: tuple[tuple[int, int], ...]
    elimination_order: tuple[int, ...]
    max_scope_groups: int
    max_domain_bits: int
    complete_graph: bool

    @property
    def exact_treewidth_if_complete(self) -> int | None:
        return self.groups - 1 if self.complete_graph else None


def audit_factor_width(
    certificate: MeasurementCertificate,
    *, forced: tuple[int, ...] = (),
) -> FactorWidthAudit:
    """Predict factor scopes for the verified measurement decomposition.

    Only nonzero lambda entries induce foreign group dependencies.
    If a clause's measured direction does not participate, it is absent
    from the factor scope.  All computations use finite graph sets and
    integer bit counts, never materializing Boolean-mask tables.
    """
    design = certificate.design
    n_groups = len(design.groups)
    if tuple(sorted(set(forced))) != forced:
        raise ValueError('forced variables must be sorted and unique')
    variable_ids = {variable for group in design.groups for variable in group}
    if any(variable not in variable_ids for variable in forced):
        raise ValueError('forced variable outside certified partition')

    scopes: list[tuple[int, ...]] = []
    for owner, occurrences in zip(design.clause_groups, certificate.occurrences):
        foreign = {
            group for occurrence in occurrences
            for group, weights in enumerate(occurrence.lambda_by_group)
            if any(weights)
        }
        scopes.append(tuple(sorted(foreign | {owner})))

    edges = tuple(sorted({
        edge for scope in scopes for edge in combinations(scope, 2)
    }))
    complete = len(edges) == n_groups * (n_groups - 1) // 2

    forced_set = set(forced)
    bits = tuple(sum(variable not in forced_set for variable in group)
                 for group in design.groups)
    max_scope = max((len(scope) for scope in scopes), default=0)
    max_bits = max((sum(bits[g] for g in scope) for scope in scopes), default=0)

    working = [set(scope) for scope in scopes]
    remaining = set(range(n_groups))
    order: list[int] = []
    while remaining:
        def scope_for(group: int) -> set[int]:
            return set().union(
                *(scope for scope in working if group in scope)
            )

        group = min(
            remaining,
            key=lambda g: (
                sum(bits[h] for h in scope_for(g)),
                len(scope_for(g)),
                g,
            ),
        )
        joined = scope_for(group)
        if joined:
            max_scope = max(max_scope, len(joined))
            max_bits = max(max_bits, sum(bits[g] for g in joined))
            working = [scope for scope in working if group not in scope]
            outgoing = joined - {group}
            if outgoing:
                working.append(outgoing)
        remaining.remove(group)
        order.append(group)
    return FactorWidthAudit(
        groups=n_groups,
        factors=len(scopes),
        measurement_rows=certificate.total_measurements,
        factor_scopes=tuple(scopes),
        interaction_edges=edges,
        elimination_order=tuple(order),
        max_scope_groups=max_scope,
        max_domain_bits=max_bits,
        complete_graph=complete,
    )
