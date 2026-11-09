"""Constructive induced-width certificates for finite factor hypergraphs.

A fixed order bounds dense *assignment slots* regardless of factor values.
This is a representation-size upper bound, not a byte or bit-time bound:
one slot may contain a large rational, a polynomial, or a nested jet.

The forest constructor provides a uniform family theorem for pairwise
interactions: leaf elimination never creates a scope of size > 2, so
group domains of size at most d have joined tables of at most d**2
slots. For s Boolean variables per group, d=2**s.

The certificate analyzes the current scope geometry using the same
independent planner used by the concrete eliminators. No dense tables
or exact-counting oracles are ever evaluated here.
"""
from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from math import prod

from non_exponential_sudoku.elimination.scope_plan import inspect_scope


@dataclass(frozen=True, slots=True)
class DenseWidthCertificate:
    order: tuple[int, ...]
    max_joined_variables: int
    max_joined_entries: int
    max_output_entries: int
    initial_factor_entries_upper: int
    joined_assignments_upper: int
    materialized_factor_entries_upper: int


def _validate(
    factors: Sequence[Sequence[int]], domain_sizes: Sequence[int],
) -> tuple[tuple[int, ...], ...]:
    n = len(domain_sizes)
    if any(type(d) is not int or d < 1 for d in domain_sizes):
        raise ValueError("Every factor variable needs a positive domain size")
    scopes: list[tuple[int, ...]] = []
    for scope in factors:
        normalized = tuple(scope)
        if len(set(normalized)) != len(normalized):
            raise ValueError("Repeated variable in factor scope")
        if any(type(v) is not int or not 0 <= v < n for v in normalized):
            raise ValueError("Factor variable outside domain")
        scopes.append(normalized)
    return tuple(scopes)


def certify_dense_order(
    factors: Sequence[Sequence[int]],
    domain_sizes: Sequence[int],
    order: Sequence[int],
) -> DenseWidthCertificate:
    """Certify scope sizes and conservative slot-work for a complete order.

    Includes *input* tables, which can be larger than all intermediate
    factors, and counts both joined and output assignment domains. The
    sums are upper bounds, not measured allocations or operation counts.
    """
    n = len(domain_sizes)
    working = list(_validate(factors, domain_sizes))
    indices = tuple(order)
    if len(indices) != n or any(type(v) is not int for v in indices) or (
        set(indices) != set(range(n))
    ):
        raise ValueError("Elimination order must contain every variable once")
    initial = sum(prod(domain_sizes[v] for v in s) for s in working)
    max_joined = max((len(s) for s in working), default=0)
    max_entries = max((prod(domain_sizes[v] for v in s) for s in working),
                      default=1)
    max_output = 1
    joined_work = 0
    materialized_upper = initial
    for variable in indices:
        step = inspect_scope(variable, working)
        join_size = prod(domain_sizes[v] for v in step.joined)
        max_joined = max(max_joined, len(step.joined))
        max_entries = max(max_entries, join_size)
        joined_work += join_size
        if step.incident:
            keep = set(step.incident)
            working = [scope for i, scope in enumerate(working) if i not in keep]
            output_entries = prod(domain_sizes[v] for v in step.output)
            max_output = max(max_output, output_entries)
            materialized_upper += output_entries
            if step.output:
                working.append(step.output)
    if any(working):
        raise AssertionError("Variable survived a complete elimination order")
    return DenseWidthCertificate(
        order=indices, max_joined_variables=max_joined,
        max_joined_entries=max_entries,
        max_output_entries=max_output,
        initial_factor_entries_upper=initial,
        joined_assignments_upper=joined_work,
        materialized_factor_entries_upper=materialized_upper,
    )


def forest_leaf_order(
    factors: Sequence[Sequence[int]], domain_sizes: Sequence[int],
) -> tuple[int, ...]:
    """Construct a bounded-width order for pairwise *forests*.

    Acyclicity is checked, not assumed. Deterministically remove the
    smallest numbered leaf at each step. An isolated variable is a leaf.
    Complexity of finding the order is polynomial in graph size.
    """
    scopes = _validate(factors, domain_sizes)
    n = len(domain_sizes)
    adjacency: list[set[int]] = [set() for _ in range(n)]
    parent = list(range(n))

    def find(value: int) -> int:
        while parent[value] != value:
            parent[value] = parent[parent[value]]
            value = parent[value]
        return value

    for scope in scopes:
        if len(scope) > 2:
            raise ValueError("Not a pairwise forest: factor arity exceeds 2")
        if len(scope) == 2:
            a, b = scope
            if b in adjacency[a]:
                continue
            if find(a) == find(b):
                raise ValueError("Not a forest: primal graph contains a cycle")
            parent[find(a)] = find(b)
            adjacency[a].add(b)
            adjacency[b].add(a)
    remaining = set(range(n))
    order: list[int] = []
    while remaining:
        leaves = (v for v in remaining if len(adjacency[v]) <= 1)
        leaf = min(leaves)
        order.append(leaf)
        remaining.remove(leaf)
        for neighbor in tuple(adjacency[leaf]):
            adjacency[neighbor].remove(leaf)
        adjacency[leaf].clear()
    return tuple(order)
