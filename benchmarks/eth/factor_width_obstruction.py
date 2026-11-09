"""Reproducible certified clique-width witness for ETH Taylor factorization.

Run: PYTHONPATH=src:. python -m benchmarks.eth.factor_width_obstruction

Every group uses at most r-1 coordinate measurement rows, each with L1=1.
A pairwise cross-group clause creates every edge of K_r.  Implication
cycles force the boundary variables in each group equal with at most
three literal occurrences per boundary variable.  Independent local
two/three-literal clauses pad n while keeping each variable active.
All replacements are identity polynomials (degree zero).

The resulting group-factor graph is K_r, so its structural treewidth
is EXACTLY r-1 for any elimination order.  These are manually certified
designs, NOT instances of the paper's particular auxiliary construction
or its n-derived parameter schedule.  The large log2 domain is a
dense-table possibility, NOT a lower bound on arbitrary algorithms.
"""
from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations

from non_exponential_sudoku.eth.cnf import CNFFormula, count_bruteforce
from non_exponential_sudoku.eth.design import (
    MeasurementDesign, certify_measurements,
)
from non_exponential_sudoku.eth.factor_width import FactorWidthAudit, audit_factor_width
from non_exponential_sudoku.eth.polynomial import ReplacementSystem


@dataclass(frozen=True, slots=True)
class CliqueWitness:
    formula: CNFFormula
    design: MeasurementDesign
    group_count: int
    expected_count: int


def build_clique_witness(r: int, size: int) -> CliqueWitness:
    """Width <=3, occurrence <=3, balanced groups and exact low-rank rows.

    Each group has r-1 boundary variables and independent local
    disjunctions in any remaining positions.  This test family is
    intentionally easy to count despite its dense *group factor graph*.
    """
    if (type(r) is not int or r < 3 or type(size) is not int
            or size < r - 1 or size - (r - 1) == 1):
        raise ValueError('require r>=3 and a group size with no singleton padding')

    def variable(group: int, position: int) -> int:
        return group * size + position + 1

    neighbors = tuple(tuple(h for h in range(r) if h != g) for g in range(r))
    boundaries = {
        (g, h): variable(g, neighbors[g].index(h))
        for g in range(r) for h in neighbors[g]
    }
    clauses: list[tuple[int, ...]] = []
    ownership: dict[frozenset[int], int] = {}

    def add(clause: tuple[int, ...], owner: int) -> None:
        key = frozenset(clause)
        if key in ownership:
            raise AssertionError('duplicate witness clause')
        ownership[key] = owner
        clauses.append(clause)

    # One two-literal cross clause for every unordered pair of groups.
    for g, h in combinations(range(r), 2):
        add((boundaries[g, h], boundaries[h, g]), g)

    # One directed implication cycle per group forces all its boundary
    # variables equal, with two local + one cross occurrence each.
    for g in range(r):
        local = [boundaries[g, h] for h in neighbors[g]]
        for i in range(len(local)):
            add((-local[i], local[(i + 1) % len(local)]), g)

    expected_multiplier = 1
    padding = size - (r - 1)
    for g in range(r):
        start = r - 1
        if padding % 2:
            add(tuple(variable(g, start + i) for i in range(3)), g)
            start += 3
            expected_multiplier *= 7
        for i in range(start, size, 2):
            add((variable(g, i), variable(g, i + 1)), g)
            expected_multiplier *= 3

    formula = CNFFormula(r * size, tuple(clauses))
    if len(formula.clauses) != len(clauses):
        raise AssertionError('canonicalization changed the clique witness')
    owners = tuple(ownership[frozenset(clause)] for clause in formula.clauses)
    groups = tuple(tuple(range(g * size, (g + 1) * size))
                   for g in range(r))
    matrices = tuple(tuple(
        tuple(int(index == coordinate) for index in range(size))
        for coordinate in range(r - 1)
    ) for _ in range(r))
    rows = r * (r - 1)
    design = MeasurementDesign(
        groups=groups, clause_groups=owners, matrices=matrices,
        tau=Fraction(rows, 2 * formula.nvars), D=1,
    )

    if max(map(len, formula.clauses), default=0) > 3:
        raise AssertionError('clause width exceeded three')
    occurrences = Counter(abs(v) for clause in formula.clauses for v in clause)
    if len(occurrences) != formula.nvars or max(occurrences.values()) > 3:
        raise AssertionError('width/occurrence bound or active variables violated')
    if not formula.nvars <= sum(len(c) for c in formula.clauses) <= 3 * formula.nvars:
        raise AssertionError('paper incidence interval violated')
    return CliqueWitness(formula, design, r, (r + 1) * expected_multiplier)


def certified_witness_profile(r: int, size: int) -> dict[str, object]:
    """Actually certify every clause then derive the group interaction width."""
    witness = build_clique_witness(r, size)
    formula, design = witness.formula, witness.design
    cert = certify_measurements(
        formula, ReplacementSystem.identity(formula), design, at=Fraction(1))
    audit: FactorWidthAudit = audit_factor_width(cert)
    expected_edges = r * (r - 1) // 2
    if (len(audit.interaction_edges) != expected_edges or
            not audit.complete_graph or audit.max_scope_groups != r):
        raise ArithmeticError('independent witness did not produce K_r')
    if audit.measurement_rows != r * (r - 1):
        raise ArithmeticError('measurement count changed')
    lam = (formula.nvars - 1).bit_length()
    return {
        'r': r, 'nvars': formula.nvars, 'lambda_bits': lam,
        'clauses': len(formula.clauses),
        'literal_incidence': sum(map(len, formula.clauses)),
        'max_occurrences': 3, 'max_clause_width': 3 if (size-r+1) % 2 else 2,
        'measurement_rows': cert.total_measurements,
        'measurement_D': design.D,
        'tau': str(design.tau),
        'illustrative_target_tau': str(Fraction(1, r * lam)),
        'tau_bound_met': design.tau <= Fraction(1, r * lam),
        'graph_edges': len(audit.interaction_edges),
        'complete_group_graph': audit.complete_graph,
        'exact_group_treewidth': audit.exact_treewidth_if_complete,
        'max_induced_scope_groups': audit.max_scope_groups,
        'log2_largest_dense_factor_domain': audit.max_domain_bits,
        'count_from_independent_formula': witness.expected_count,
        'paper_parameter_schedule_admitted': False,
    }


def probe() -> dict[str, object]:
    small = build_clique_witness(3, 2)
    if count_bruteforce(small.formula) != small.expected_count:
        raise ArithmeticError('small clique #SAT oracle mismatch')
    return {
        'status': 'certified-design-structural-obstruction-not-hardness-proof',
        'witnesses': [certified_witness_profile(3, 22),
                      certified_witness_profile(4, 48)],
    }


def main() -> None:
    print(json.dumps(probe(), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
