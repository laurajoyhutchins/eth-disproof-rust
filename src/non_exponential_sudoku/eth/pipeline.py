"""Auditable, bounded end-to-end reference for the October 25 CNF construction.

This is deliberately NOT a general subexponential #SAT solver. Every
nontrivial leaf uses certified auxiliary measurements, separated Taylor
coefficients, and Hermite reconstruction; only 0/1-variable leaves use
an explicitly reported two-assignment base case. No counting oracle or
alternative solver is called if construction exceeds its resource budgets.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal

from non_exponential_sudoku.runtime.budget import CapacityError

from .backends import ArithmeticBackend
from .balance import BalanceLimits
from .cnf import CNFFormula
from .construction import ConstructionLimits, construct_bounded_designs
from .interpolation import (
    HermiteLimits, _degree_upper_bound, count_from_manual_designs,
)
from .preprocess import ReductionLimits, prepare_bounded_cnf
from .sparsification import (
    SparsificationLimits, SparsificationParameters, iter_disjoint_leaves,
    reference_sparsification_parameters,
)
from .taylor import TaylorLimits


@dataclass(frozen=True, slots=True)
class ReferencePipelineConfig:
    """Named parameters, separate from the paper's quantitative admission.

    A low sparsification threshold is for finite experiments, NOT an
    invocation of the theorem's tree-size guarantee. To use the paper
    threshold, supply paper_sparsification_parameters explicitly.
    """

    sparsification: SparsificationParameters = field(
        default_factory=lambda: reference_sparsification_parameters(3, 2)
    )
    r: int = 2
    Q: int = 2
    R: int = 2
    schedule: Literal['conditional', 'digits'] = 'conditional'
    backend: ArithmeticBackend = 'python'
    max_leaves: int = 64
    max_output_bits: int = 1_000_000
    reduction_limits: ReductionLimits = ReductionLimits()
    sparsification_limits: SparsificationLimits = SparsificationLimits()
    construction_limits: ConstructionLimits = ConstructionLimits()
    balance_limits: BalanceLimits = BalanceLimits()
    taylor_limits: TaylorLimits = TaylorLimits()
    hermite_limits: HermiteLimits = HermiteLimits()

    def __post_init__(self) -> None:
        if any(type(value) is not int or value < 1 for value in (
            self.r, self.Q, self.R, self.max_leaves, self.max_output_bits
        )):
            raise ValueError('pipeline dimensions and budgets must be positive integers')
        if self.r < 2 or self.R > self.Q + 1:
            raise ValueError('pipeline requires r>=2 and R<=Q+1')
        if self.schedule not in ('conditional', 'digits'):
            raise ValueError('unknown reference construction schedule')
        if self.backend not in ('python', 'flint'):
            raise ValueError('unknown exact arithmetic backend')


@dataclass(frozen=True, slots=True)
class ReferenceLeafEvidence:
    """Count contribution after restoring this leaf's free variables."""

    path: tuple[str, ...]
    leaf_variables: int
    prepared_variables: int
    free_bits: int
    reduced_count: int
    contribution: int
    method: Literal['two-assignment-base', 'certified-construction']
    centers: int
    taylor_pairs: int
    measurement_tuples: int
    hermite_operations: int
    max_coefficient_bits: int


@dataclass(frozen=True, slots=True)
class ReferencePipelineResult:
    """Complete count only; partial leaf sums are never returned."""

    count: int
    source_variables: int
    source_clauses: int
    source_width_reduced: bool
    outer_free_bits: int
    sparsification_theorem_threshold: bool
    leaves: tuple[ReferenceLeafEvidence, ...]
    algorithm_status: str = 'bounded-constructive-reference; no asymptotic guarantee'


def _bounded_add(left: int, right: int, *, max_bits: int) -> int:
    result = left + right
    if result.bit_length() > max_bits:
        raise CapacityError('ETH end-to-end count output bit limit')
    return result


def _evaluate_leaf(
    formula: CNFFormula, path: tuple[str, ...], config: ReferencePipelineConfig,
) -> ReferenceLeafEvidence:
    # Every leaf is projected and re-reduced. A sparsification branch can
    # create new occurrences even if its parent already met the bound.
    prepared = prepare_bounded_cnf(formula, limits=config.reduction_limits)
    reduced = prepared.formula

    if reduced.nvars <= 1:
        # Explicit finite base case, at most TWO assignments. This is not
        # a variable-size Boolean-cube or a hidden general #SAT fallback.
        reduced_count = sum(int(reduced.satisfied_mask(mask))
                            for mask in range(1 << reduced.nvars))
        method: Literal['two-assignment-base', 'certified-construction'] = 'two-assignment-base'
        centers = taylor_pairs = measurement_tuples = hermite_operations = max_bits = 0
    else:
        construction = construct_bounded_designs(
            reduced, r=config.r, Q=config.Q, R=config.R,
            schedule=config.schedule,
            limits=config.construction_limits,
            balance_limits=config.balance_limits,
        )
        # Match the existing count_from_constructed convention. The degree
        # is a verified upper bound, never inferred from the answer.
        degree = _degree_upper_bound(construction.replacements)
        order = degree // len(construction.centers)
        reconstructed = count_from_manual_designs(
            reduced, construction.centers, construction.replacements,
            order=order, backend=config.backend,
            taylor_limits=config.taylor_limits,
            hermite_limits=config.hermite_limits,
        )
        reduced_count = reconstructed.count
        method = 'certified-construction'
        centers = len(reconstructed.taylor_data)
        taylor_pairs = sum(item.stats.taylor_pairs for item in reconstructed.taylor_data)
        measurement_tuples = sum(item.stats.measurement_tuples
                                 for item in reconstructed.taylor_data)
        hermite_operations = reconstructed.hermite_stats.rational_operations
        max_bits = max(
            (item.stats.max_coefficient_bits for item in reconstructed.taylor_data),
            default=0,
        )
        max_bits = max(max_bits, reconstructed.hermite_stats.max_coefficient_bits)

    contribution = prepared.restore_count(
        reduced_count, max_output_bits=config.max_output_bits,
    )
    return ReferenceLeafEvidence(
        path=path, leaf_variables=formula.nvars,
        prepared_variables=reduced.nvars,
        free_bits=prepared.projection.free_bits,
        reduced_count=reduced_count, contribution=contribution, method=method,
        centers=centers, taylor_pairs=taylor_pairs,
        measurement_tuples=measurement_tuples,
        hermite_operations=hermite_operations, max_coefficient_bits=max_bits,
    )


def count_cnf_reference(
    formula: CNFFormula, *, config: ReferencePipelineConfig = ReferencePipelineConfig(),
) -> ReferencePipelineResult:
    """Normalize -> disjoint leaves -> parsimonious reductions -> certified count.

    The original formula has its declared-variable semantics throughout.
    Width > sparsification.k is reduced *before* branching; its free-variable
    multiplier is restored once after the entire disjoint leaf sum.
    Every generated leaf must finish successfully for a result to be returned.
    No external #SAT oracle, full-cube fallback, or silent branch skipping.
    """
    if not isinstance(formula, CNFFormula):
        raise TypeError('expected CNFFormula')
    params = config.sparsification
    width_reduced = any(len(clause) > params.k for clause in formula.clauses)
    initial = (prepare_bounded_cnf(formula, limits=config.reduction_limits)
               if width_reduced else None)
    working = initial.formula if initial is not None else formula

    evidence: list[ReferenceLeafEvidence] = []
    subtotal = 0
    for leaf in iter_disjoint_leaves(
        working, params, limits=config.sparsification_limits,
    ):
        if len(evidence) >= config.max_leaves:
            raise CapacityError('ETH end-to-end leaf evaluation limit')
        result = _evaluate_leaf(leaf.formula, leaf.path, config)
        evidence.append(result)
        subtotal = _bounded_add(
            subtotal, result.contribution, max_bits=config.max_output_bits,
        )

    if not evidence:
        raise ArithmeticError('sparsification produced no leaves')
    outer_free_bits = initial.projection.free_bits if initial is not None else 0
    count = (initial.restore_count(subtotal, max_output_bits=config.max_output_bits)
             if initial is not None else subtotal)
    if count.bit_length() > config.max_output_bits:
        raise CapacityError('ETH end-to-end count output bit limit')
    # Compare bit lengths first; avoid building a huge bound for inputs with
    # many declared-but-unused variables.
    bits = count.bit_length()
    if (bits > formula.nvars + 1 or
            (bits == formula.nvars + 1 and count != (1 << formula.nvars))):
        raise ArithmeticError('end-to-end count exceeds the declared Boolean cube')
    return ReferencePipelineResult(
        count=count, source_variables=formula.nvars,
        source_clauses=len(formula.clauses),
        source_width_reduced=width_reduced, outer_free_bits=outer_free_bits,
        sparsification_theorem_threshold=params.theorem_threshold,
        leaves=tuple(evidence),
    )
