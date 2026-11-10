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


@dataclass(frozen=True, slots=True)
class GridMinorCertificate:
    """Finite checked grid minor plus a mathematical tw >= side-1 premise."""

    grid_side: int
    variables: int
    clauses: int
    literal_occurrences: int
    maximum_occurrences: int
    maximum_clause_width: int
    contracted_grid_edges: int
    treewidth_lower_bound: int


def _wall_side(side: int) -> int:
    if type(side) is not int or side < 2 or side & (side - 1) or side > 16:
        raise ValueError("grid side must be a power of two from 2 through 16")
    return side


def subcubic_grid_cnf(side: int) -> CNFFormula:
    """2-CNF whose primal graph contains a side x side grid minor.

    Replace every square-grid vertex with a four-cycle of ports N,E,S,W.
    Attach each original grid edge to its corresponding single port.
    The new graph has maximum degree 3. Contracting each port four-cycle
    recovers the original grid. Therefore its treewidth is >= side-1,
    using the standard pairwise-touching row/column cross bramble.

    n=4*side**2, clauses=6*side**2-2*side, M=12*side**2-4*side,
    maximum occurrence 3, maximum clause width 2.
    """
    k = _wall_side(side)

    def port(row: int, col: int, direction: int) -> int:
        return 4 * (row * k + col) + direction + 1

    clauses: list[tuple[int, int]] = []
    for row in range(k):
        for col in range(k):
            for left, right in ((0, 1), (1, 2), (2, 3), (3, 0)):
                clauses.append((port(row, col, left), port(row, col, right)))
            if col + 1 < k:
                clauses.append((port(row, col, 1), port(row, col + 1, 3)))
            if row + 1 < k:
                clauses.append((port(row, col, 2), port(row + 1, col, 0)))
    return CNFFormula(4 * k * k, tuple(clauses))


def certify_subcubic_grid_minor(
    formula: CNFFormula, *, side: int,
) -> GridMinorCertificate:
    """Check every port-cycle and every inter-cell grid edge by endpoints.

    The graph-minor lower bound itself follows from contracting the
    independently checked port cycles. This check does NOT establish
    an exponential exact-counting lower bound for this CNF family.
    """
    k = _wall_side(side)
    n = 4 * k * k
    if formula.nvars != n:
        raise ValueError("grid-minor formula variable dimension mismatch")
    edges: set[frozenset[int]] = set()
    counts = [0] * n
    for clause in formula.clauses:
        if len(clause) != 2 or any(lit <= 0 for lit in clause):
            raise ValueError("grid-minor clauses must be positive binary edges")
        left, right = clause[0] - 1, clause[1] - 1
        if left == right:
            raise ValueError("self-edge in minor certificate")
        edges.add(frozenset((left, right)))
        counts[left] += 1
        counts[right] += 1

    def port(row: int, col: int, direction: int) -> int:
        return 4 * (row * k + col) + direction

    expected: set[frozenset[int]] = set()
    contracted: set[frozenset[int]] = set()
    for row in range(k):
        for col in range(k):
            for left, right in ((0, 1), (1, 2), (2, 3), (3, 0)):
                expected.add(frozenset((port(row, col, left), port(row, col, right))))
            if col + 1 < k:
                expected.add(frozenset((port(row, col, 1), port(row, col + 1, 3))))
                contracted.add(frozenset((row * k + col, row * k + col + 1)))
            if row + 1 < k:
                expected.add(frozenset((port(row, col, 2), port(row + 1, col, 0))))
                contracted.add(frozenset((row * k + col, (row + 1) * k + col)))
    if edges != expected or len(formula.clauses) != len(edges):
        raise ValueError("actual clauses differ from the grid-port minor")
    if max(counts) > 3:
        raise ArithmeticError("grid-port degree exceeds three")
    return GridMinorCertificate(
        grid_side=k, variables=n,
        clauses=len(edges), literal_occurrences=2 * len(edges),
        maximum_occurrences=max(counts),
        maximum_clause_width=2,
        contracted_grid_edges=len(contracted),
        treewidth_lower_bound=k - 1,
    )
