"""Finite bounded-incidence CNF fixtures with explicit, LIMITED claims.

These positive-literal families are satisfiable by the all-ones assignment.
The cyclic family has an easy elimination order; the affine family has a
wider *chosen* ordering, which does not lower-bound treewidth. The grid-port
family has a certified square-grid minor but admits subexponential row DP.
Neither numeric paper admission nor treewidth is a #SAT hardness witness.
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


@dataclass(frozen=True, slots=True)
class VirtualSubcubicGridStep5:
    """Symbolic bounded-incidence and grid-minor certificate, no giant graph."""

    lambda_bits: int
    grid_side_expression: str
    variables_expression: str
    clauses_expression: str
    literal_occurrences_expression: str
    treewidth_lower_bound_expression: str
    r: int
    Q: int
    R: int
    spectral_dimension_squared_log2_upper: int
    spectral_overview_margin_proved: bool
    numeric_step5_admitted: bool
    materialized_cnf: bool = False
    executed_paper_algorithm: bool = False
    executed_lean_machine: bool = False


def virtual_subcubic_grid_step5(lambda_bits: int) -> VirtualSubcubicGridStep5:
    """Extend the coupled Step-5 numeric audit to a proven grid-minor family.

    For even lambda, let k=2**((lambda-2)//2), n=4*k*k=2**lambda.
    The wall has b=3,w=2 and M=(3-1/k)*n, with k>=2.

    Compare to the already-admitted cyclic b=3,w=3,M=3n family:
    every numeric check except balancing incidence and the stronger
    12D**2 overview inequality is unchanged or weaker.
    The additional independently tested symbolic sufficient condition
        4*Q*ceil(log2(r)) <= lambda-3
    yields D**2 <= n/8. Therefore both
        2*(3+2)*D**2 <= 10*n/8 <= M
        12*D**2 <= 12*n/8 <= M
    hold because M>=5n/2. This is arithmetic admission, NOT a
    proof of #SAT hardness or of the source's unbounded execution.
    """
    from non_exponential_sudoku.eth.paper_admitted_witness import (
        virtual_coupled_3cnf_step5,
    )

    if type(lambda_bits) is not int or lambda_bits < 4 or lambda_bits % 2:
        raise ValueError("even lambda at least four required for wall grid")
    witness = virtual_coupled_3cnf_step5(lambda_bits)
    if not witness.admitted_by_sufficient_conditions:
        raise ValueError("coupled Step-5 base sufficient conditions unproved")
    D2_log_upper = 4 * witness.Q * (witness.r - 1).bit_length()
    # ceil(log2(r)) bounds log2(r) without constructing D=r**(2Q).
    if D2_log_upper > lambda_bits - 3:
        raise ValueError("wall incidence/overview margin unproved")
    exponent = (lambda_bits - 2) // 2
    k = f"2**{exponent}"
    n = f"2**{lambda_bits}"
    return VirtualSubcubicGridStep5(
        lambda_bits=lambda_bits,
        grid_side_expression=k,
        variables_expression=n,
        clauses_expression=f"6*({k})**2-2*({k})",
        literal_occurrences_expression=f"3*({n})-4*({k})",
        treewidth_lower_bound_expression=f"({k})-1",
        r=witness.r, Q=witness.Q, R=witness.R,
        spectral_dimension_squared_log2_upper=D2_log_upper,
        spectral_overview_margin_proved=True,
        numeric_step5_admitted=True,
    )


def alternating_signs(formula: CNFFormula) -> CNFFormula:
    """Change Boolean semantics without changing the unsigned incidence graph.

    Flip a literal when clause_index + its 1-based variable index is even.
    Every clause keeps the same variables and width. This is a finite
    *signed fixture*, not a claim that its #SAT count is difficult.
    """
    return CNFFormula(formula.nvars, tuple(
        tuple(-abs(literal) if (index + abs(literal)) % 2 == 0
              else abs(literal) for literal in clause)
        for index, clause in enumerate(formula.clauses)
    ))
