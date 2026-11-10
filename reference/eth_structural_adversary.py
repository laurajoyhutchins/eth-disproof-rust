"""Finite structural stress probes for the bounded-occurrence ETH claim.

A cyclic triple-clause CNF is Step-5-admissible symbolically but has
constant-width natural elimination: it cannot challenge worst-case claims.
The affine three-permutation construction retains the SAME M=3n,b=w=3
incidence profile yet produces wider natural-order traces on finite sizes.

An elimination width for ONE ordering is only an UPPER bound on treewidth.
No expansion, hard #SAT instance, treewidth lower bound, or ETH
counterexample is asserted here. The materialization cap is intentional.
"""
from __future__ import annotations

from dataclasses import dataclass

from non_exponential_sudoku.eth.cnf import CNFFormula


def _size(n: int) -> int:
    if type(n) is not int or n < 8 or n & (n - 1):
        raise ValueError("require a power of two with n>=8")
    if n > 512:
        raise ValueError("finite structural probe cap of 512 variables")
    return n


def cyclic_three_cnf(n: int) -> CNFFormula:
    n = _size(n)
    return CNFFormula(n, tuple(
        (i + 1, (i + 1) % n + 1, (i + 2) % n + 1)
        for i in range(n)
    ))


def affine_three_cnf(n: int) -> CNFFormula:
    """Each vertex has three occurrences and all clauses are distinct.

    Id, 3i+1, and 5i+2 modulo 2^k are permutations or distinct entries:
    3 and 5 are odd (units); pairwise differences 2i+1, 4i+2,
    and 2i+1 are odd or 2 modulo 4, never zero modulo 2^k for k>=3.

    The member 3i+1 has parity opposite to the other two. Any equal
    unordered clauses thus have the same unique opposite-parity vertex;
    invertibility of 3 forces the same index i. Consequently no
    normalization step removes duplicates, and M=3n exactly.
    """
    n = _size(n)
    return CNFFormula(n, tuple(
        (i + 1, (3 * i + 1) % n + 1, (5 * i + 2) % n + 1)
        for i in range(n)
    ))


@dataclass(frozen=True, slots=True)
class NaturalEliminationProfile:
    variables: int
    clauses: int
    literal_occurrences: int
    maximum_variable_occurrences: int
    maximum_clause_width: int
    natural_order_induced_width: int


def natural_order_induced_width(formula: CNFFormula) -> NaturalEliminationProfile:
    """Exact induced width of elimination order 0,1,...,n-1.

    This is a *specific algorithmic trace*, NOT a treewidth lower
    bound, minimax optimization, or graph expander certificate.
    """
    n = formula.nvars
    if n < 1 or n > 512:
        raise ValueError("finite primal graph probe supports 1..512 variables")
    graph: list[set[int]] = [set() for _ in range(n)]
    counts = [0] * n
    ell = 0
    for clause in formula.clauses:
        indices = tuple(abs(lit) - 1 for lit in clause)
        ell += len(indices)
        for i, left in enumerate(indices):
            counts[left] += 1
            for right in indices[i + 1:]:
                graph[left].add(right)
                graph[right].add(left)
    peak = 0
    for vertex in range(n):
        neighbors = tuple(sorted(graph[vertex]))
        peak = max(peak, len(neighbors))
        for i, left in enumerate(neighbors):
            for right in neighbors[i + 1:]:
                graph[left].add(right)
                graph[right].add(left)
        for other in neighbors:
            graph[other].remove(vertex)
        graph[vertex].clear()
    return NaturalEliminationProfile(
        variables=n, clauses=len(formula.clauses), literal_occurrences=ell,
        maximum_variable_occurrences=max(counts, default=0),
        maximum_clause_width=max(map(len, formula.clauses), default=0),
        natural_order_induced_width=peak,
    )
