"""Disjoint #k-SAT sparsification from the October 25 manuscript appendix.

Implements the appendix's deterministic shared-literal branching rule. The
A/B branches partition the satisfying assignments, not merely cover them.
The theorem parameter selector computes the paper's threshold M exactly from
sigma. An explicitly supplied smaller threshold is a *reference experiment*
and does not carry the theorem's tree-size guarantee.

The DFS iterator holds only a bounded number of pending nodes, rather than
materializing the whole tree. Work and depth caps fail with CapacityError;
consumers must exhaust the iterator before treating a sum as complete.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from typing import Iterator

from non_exponential_sudoku.runtime.budget import CapacityError

from .cnf import CNFFormula


def _key(literal: int) -> tuple[int, bool]:
    return abs(literal), literal < 0


@dataclass(frozen=True, slots=True)
class SparsificationLimits:
    max_nodes: int = 4096
    max_depth: int = 512
    max_clauses_per_node: int = 20_000
    max_clause_width: int = 8
    max_parameter_steps: int = 256
    max_candidates_per_node: int = 1_000_000

    def __post_init__(self) -> None:
        for name in self.__dataclass_fields__:
            if type(getattr(self, name)) is not int or getattr(self, name) < 1:
                raise ValueError(f'{name} must be a positive integer')


@dataclass(frozen=True, slots=True)
class SparsificationParameters:
    k: int
    sigma: Fraction | None
    M: int
    C: int
    gamma: int
    occurrence_bound: int
    theorem_threshold: bool

    def __post_init__(self) -> None:
        if type(self.k) is not int or self.k < 2 or type(self.M) is not int or self.M < 2:
            raise ValueError('invalid sparsification k or threshold')
        C, gamma = _tree_constants(self.k, self.M)
        if ((self.C, self.gamma, self.occurrence_bound) !=
                (C, gamma, 2 * sum(self.M ** j for j in range(self.k)))):
            raise ValueError('inconsistent sparsification constants')
        if self.theorem_threshold:
            if not isinstance(self.sigma, Fraction) or not 0 < self.sigma <= 1:
                raise ValueError('theorem threshold needs exact sigma')
            if self.M < gamma or self.M & (self.M - 1):
                raise ValueError('theorem threshold must be a power of two >= gamma')
            h = (4 * C * self.M - 1).bit_length()
            if gamma * h * self.sigma.denominator > self.sigma.numerator * self.M:
                raise ValueError('theorem threshold inequality not satisfied')
            if self.M // 2 >= gamma:
                prev = self.M // 2
                Cprev, _ = _tree_constants(self.k, prev)
                hprev = (4 * Cprev * prev - 1).bit_length()
                if gamma * hprev * self.sigma.denominator <= self.sigma.numerator * prev:
                    raise ValueError('theorem threshold is not minimal')
        elif self.sigma is not None:
            raise ValueError('reference threshold cannot claim theorem sigma')


@dataclass(frozen=True, slots=True)
class SparseLeaf:
    """A disjoint leaf with its exact binary branch address."""

    formula: CNFFormula
    path: tuple[str, ...]
    parameters: SparsificationParameters


def _tree_constants(k: int, M: int) -> tuple[int, int]:
    C = 4 * sum((3 * M) ** j for j in range(k - 1))
    gamma = 4 * sum(3 ** j for j in range(k - 1))
    return C, gamma


def paper_sparsification_parameters(
    k: int, sigma: Fraction, *, limits: SparsificationLimits = SparsificationLimits(),
) -> SparsificationParameters:
    """The appendix's *first* power of two M>=Gamma with Gamma*h<=sigma*M.

    Here h=ceil(log2(4*C*M)). Integer-only arithmetic prevents a floating
    acceptance of a false theorem parameter inequality.
    """
    if type(k) is not int or not 2 <= k <= limits.max_clause_width:
        raise ValueError('k must be an integer in [2, max_clause_width]')
    if not isinstance(sigma, Fraction) or not 0 < sigma <= 1:
        raise ValueError('sigma must be an exact rational in (0,1]')
    gamma = _tree_constants(k, 2)[1]
    M = 1 << (gamma - 1).bit_length()
    for _ in range(limits.max_parameter_steps):
        C, gamma = _tree_constants(k, M)
        h = (4 * C * M - 1).bit_length()
        if gamma * h * sigma.denominator <= sigma.numerator * M:
            return SparsificationParameters(k, sigma, M, C, gamma,
                                            2 * sum(M ** j for j in range(k)), True)
        M *= 2
    raise CapacityError('ETH sparsification parameter search limit')


def reference_sparsification_parameters(
    k: int, threshold: int, *, limits: SparsificationLimits = SparsificationLimits(),
) -> SparsificationParameters:
    """Bounded diagnostic threshold; *no* paper tree-size theorem applies."""
    if type(k) is not int or not 2 <= k <= limits.max_clause_width:
        raise ValueError('k must be an integer in [2, max_clause_width]')
    if type(threshold) is not int or threshold < 2:
        raise ValueError('threshold must be an integer >=2')
    C, gamma = _tree_constants(k, threshold)
    return SparsificationParameters(k, None, threshold, C, gamma,
                                    2 * sum(threshold ** j for j in range(k)), False)


def _selected_violation(
    formula: CNFFormula, params: SparsificationParameters,
    *, max_candidates: int,
) -> tuple[int, tuple[int, ...]] | None:
    """Smallest width c, then largest heart H, then deterministic literal tie."""
    counts: dict[tuple[int, tuple[int, ...]], int] = {}
    candidates = 0
    for clause in formula.clauses:
        c = len(clause)
        if c > params.k:
            raise ValueError('CNF width exceeds declared k')
        if c < 2:
            continue
        for size in range(1, c):
            for H in combinations(clause, size):
                candidates += 1
                if candidates > max_candidates:
                    raise CapacityError('ETH sparsification candidate work limit')
                key = (c, H)
                counts[key] = counts.get(key, 0) + 1
    eligible = (key for key, deg in counts.items()
                if deg >= params.M ** (key[0] - len(key[1])))
    # Canonical tie-breaking must use numeric literal order, not DIMACS sign.
    return min(eligible, key=lambda x: (x[0], -len(x[1]), tuple(map(_key, x[1]))),
               default=None)


def _children(formula: CNFFormula, c: int, heart: tuple[int, ...]) -> tuple[CNFFormula, CNFFormula]:
    H = frozenset(heart)
    selected: list[tuple[int, ...]] = []
    other: list[tuple[int, ...]] = []
    for clause in formula.clauses:
        if len(clause) == c and H.issubset(clause):
            selected.append(clause)
        else:
            other.append(clause)
    if not selected:
        raise ArithmeticError('sparsification selected an absent shared heart')
    petals = [tuple(lit for lit in clause if lit not in H) for clause in selected]
    # A: H is true, so all selected clauses vanish. B: H is false, so every
    # petal must be true. Each negative unit is a literal, NOT a negated clause.
    branch_a = CNFFormula(formula.nvars, tuple((*other, heart)))
    branch_b = CNFFormula(formula.nvars, tuple((*other, *petals,
                                             *((-lit,) for lit in heart))))
    return branch_a, branch_b


def iter_disjoint_leaves(
    formula: CNFFormula, params: SparsificationParameters, *,
    limits: SparsificationLimits = SparsificationLimits(),
) -> Iterator[SparseLeaf]:
    """Yield disjoint leaves, or refuse explicitly upon exceeding work caps.

    `path` is an exact branch address; all original satisfying assignments
    occur in exactly one complete leaf. Incomplete generators (from budgets
    or early consumer termination) do not represent a completed partition.
    """
    if len(formula.clauses) > limits.max_clauses_per_node:
        raise CapacityError('ETH sparsification clause limit')
    if any(len(clause) > params.k for clause in formula.clauses):
        raise ValueError('CNF clause width exceeds k')
    nodes = 0
    pending: list[tuple[CNFFormula, tuple[str, ...]]] = [(formula, ())]
    while pending:
        node, path = pending.pop()
        nodes += 1
        if nodes > limits.max_nodes:
            raise CapacityError('ETH sparsification node limit')
        if len(node.clauses) > limits.max_clauses_per_node:
            raise CapacityError('ETH sparsification clause limit')
        if params.theorem_threshold and (
            len(path) > params.C * formula.nvars or
            path.count('B') * params.M > params.gamma * formula.nvars
        ):
            raise ArithmeticError('sparsification tree bound violated')
        violation = _selected_violation(node, params,
                                        max_candidates=limits.max_candidates_per_node)
        if violation is None:
            occurrences = [0] * node.nvars
            for clause in node.clauses:
                for lit in clause:
                    occurrences[abs(lit) - 1] += 1
            if any(c > params.occurrence_bound for c in occurrences):
                raise ArithmeticError('sparsification leaf occurrence bound violated')
            yield SparseLeaf(node, path, params)
            continue
        if len(path) >= limits.max_depth:
            raise CapacityError('ETH sparsification depth limit')
        a, b = _children(node, *violation)
        for child in (a, b):
            if len(child.clauses) > limits.max_clauses_per_node:
                raise CapacityError('ETH sparsification child clause limit')
        pending.append((b, (*path, 'B')))
        pending.append((a, (*path, 'A')))
