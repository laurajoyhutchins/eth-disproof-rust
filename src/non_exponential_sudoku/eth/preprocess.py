"""Parsimonious CNF width and occurrence reductions (overview, Sec. 2).

An OR-gate Tseitin encoding has a unique gate assignment for each input
assignment.  Tovey's directed implication cycle forces all occurrence copies
of a variable to agree and likewise has one extension.  Original variables
which are replaced by copies are *not* kept as unused declared variables.

This reduction does not implement disjoint sparsification, nor does it imply
an ETH runtime bound for the resulting number of variables.
"""
from __future__ import annotations

from dataclasses import dataclass

from non_exponential_sudoku.runtime.budget import CapacityError

from .cnf import CNFFormula


@dataclass(frozen=True, slots=True)
class ReductionLimits:
    max_variables: int = 100_000
    max_clauses: int = 300_000
    max_literal_occurrences: int = 1_000_000

    def __post_init__(self) -> None:
        for name in self.__dataclass_fields__:
            if type(getattr(self, name)) is not int or getattr(self, name) < 1:
                raise ValueError(f'{name} must be a positive integer')


@dataclass(frozen=True, slots=True)
class ParsimoniousReduction:
    formula: CNFFormula
    original_variables: int
    width_three_variables: int
    original_clauses: int
    output_occurrences: int


def _check_size(nvars: int, clauses: list[tuple[int, ...]], limits: ReductionLimits) -> None:
    if nvars > limits.max_variables:
        raise CapacityError('ETH preprocessing variable limit')
    if len(clauses) > limits.max_clauses:
        raise CapacityError('ETH preprocessing clause limit')
    if sum(len(clause) for clause in clauses) > limits.max_literal_occurrences:
        raise CapacityError('ETH preprocessing literal occurrence limit')


def reduce_width_occurrences(
    formula: CNFFormula, *, limits: ReductionLimits = ReductionLimits(),
) -> ParsimoniousReduction:
    """Construct 3-CNF with <=3 literal occurrences per declared variable.

    Counts remain equal on the FULL declared Boolean cubes, not merely after
    projection.  Each introduced Boolean value is uniquely forced by the
    original assignment. The output is canonically normalized afterward.
    """
    _check_size(formula.nvars, list(formula.clauses), limits)
    next_var = formula.nvars
    width3: list[tuple[int, ...]] = []

    def gate(u: int, v: int) -> int:
        nonlocal next_var
        next_var += 1
        _check_size(next_var, width3, limits)
        z = next_var
        width3.extend(((-u, z), (-v, z), (u, v, -z)))
        _check_size(next_var, width3, limits)
        return z

    for clause in formula.clauses:
        if len(clause) <= 3:
            width3.append(clause)
        else:
            running = gate(clause[0], clause[1])
            for literal in clause[2:]:
                running = gate(running, literal)
            width3.append((running,))
        _check_size(next_var, width3, limits)
    intermediate = CNFFormula(next_var, tuple(width3))
    counts = [0] * (intermediate.nvars + 1)
    for clause in intermediate.clauses:
        for lit in clause:
            counts[abs(lit)] += 1

    # A variable with >=2 occurrences is replaced, not left dangling.
    # Variables with 0 occurrences are retained to preserve free-bit factors.
    unchanged: dict[int, int] = {}
    final_var = 0
    for old in range(1, intermediate.nvars + 1):
        if counts[old] <= 1:
            final_var += 1
            unchanged[old] = final_var
    copies: dict[int, list[int]] = {old: [] for old in range(1, intermediate.nvars + 1)
                                     if counts[old] >= 2}
    final_clauses: list[tuple[int, ...]] = []
    for clause in intermediate.clauses:
        mapped: list[int] = []
        for literal in clause:
            old = abs(literal)
            if counts[old] <= 1:
                new = unchanged[old]
            else:
                final_var += 1
                new = final_var
                copies[old].append(new)
            mapped.append(new if literal > 0 else -new)
        final_clauses.append(tuple(mapped))
    _check_size(final_var, final_clauses, limits)
    for old in sorted(copies):
        assigned = copies[old]
        if len(assigned) != counts[old] or len(assigned) < 2:
            raise ArithmeticError('Tovey occurrence assignment invariant failed')
        for i, v in enumerate(assigned):
            final_clauses.append((-v, assigned[(i + 1) % len(assigned)]))
        _check_size(final_var, final_clauses, limits)
    result = CNFFormula(final_var, tuple(final_clauses))
    if any(len(clause) > 3 for clause in result.clauses):
        raise ArithmeticError('width reduction failed')
    occurrence_counts = [0] * (result.nvars + 1)
    for clause in result.clauses:
        for lit in clause:
            occurrence_counts[abs(lit)] += 1
    if max(occurrence_counts, default=0) > 3:
        raise ArithmeticError('occurrence reduction failed')
    return ParsimoniousReduction(result, formula.nvars, intermediate.nvars,
                                len(formula.clauses), sum(len(c) for c in result.clauses))


@dataclass(frozen=True, slots=True)
class FreeVariableProjection:
    """Reindexed active variables plus a count multiplier of 2**free_bits.

    This is NOT a parsimonious reduction: the multiplier must be restored.
    `old_variables` maps each new 1-indexed variable to an old variable.
    """

    formula: CNFFormula
    original_nvars: int
    old_variables: tuple[int, ...]

    @property
    def free_bits(self) -> int:
        return self.original_nvars - len(self.old_variables)

    def restore_count(self, reduced_count: int, *, max_output_bits: int = 1_000_000) -> int:
        """Restore the original declared-variable count without allocating blindly."""
        if type(reduced_count) is not int or reduced_count < 0:
            raise ValueError('reduced_count must be a nonnegative integer')
        if type(max_output_bits) is not int or max_output_bits < 1:
            raise ValueError('max_output_bits must be a positive integer')
        if reduced_count and reduced_count.bit_length() + self.free_bits > max_output_bits:
            raise CapacityError('ETH restored model-count bit limit')
        return reduced_count << self.free_bits


def project_free_variables(formula: CNFFormula) -> FreeVariableProjection:
    """Remove declared variables absent from every normalized clause.

    The formula has exactly 2**free_bits times the count of the result.
    Literal signs and the original assignment-to-reduced-assignment
    correspondence are preserved. No SAT solving or enumeration is performed.
    """
    active = tuple(sorted({abs(lit) for clause in formula.clauses for lit in clause}))
    to_new = {old: i + 1 for i, old in enumerate(active)}
    clauses = tuple(tuple(to_new[abs(lit)] if lit > 0 else -to_new[-lit]
                          for lit in clause) for clause in formula.clauses)
    return FreeVariableProjection(CNFFormula(len(active), clauses), formula.nvars, active)


@dataclass(frozen=True, slots=True)
class PreparedBoundedCNF:
    """Count equivalence: count(original) = 2**free_bits * count(reduced)."""

    projection: FreeVariableProjection
    occurrence_reduction: ParsimoniousReduction

    @property
    def formula(self) -> CNFFormula:
        return self.occurrence_reduction.formula

    def restore_count(self, reduced_count: int, *, max_output_bits: int = 1_000_000) -> int:
        return self.projection.restore_count(reduced_count, max_output_bits=max_output_bits)


def prepare_bounded_cnf(
    formula: CNFFormula, *, limits: ReductionLimits = ReductionLimits(),
) -> PreparedBoundedCNF:
    """Width/occurrence reduction with explicit free-variable multiplicity.

    This does NOT supply disjoint sparsification or its number-of-branches
    bound. It may increase the variable count by O(original CNF size).
    """
    # Check source clause/occurrence work before building the active index.
    # A large declared-variable dimension alone is acceptable: free bits are
    # represented as an exponent, not as an allocated Boolean vector.
    if (len(formula.clauses) > limits.max_clauses or
            sum(len(clause) for clause in formula.clauses) > limits.max_literal_occurrences):
        raise CapacityError('ETH preprocessing source clause/occurrence limit')
    projection = project_free_variables(formula)
    reduced = reduce_width_occurrences(projection.formula, limits=limits)
    return PreparedBoundedCNF(projection, reduced)
