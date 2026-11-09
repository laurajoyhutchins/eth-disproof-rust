"""Exact bounded #SAT reference constructions."""

from .cnf import CNFFormula, count_bruteforce
from .polynomial import Polynomial, ReferenceLimits, ReplacementForm, ReplacementSystem, clause_satisfaction_polynomial, deformation_polynomial
from .design import CertifiedOccurrence, MeasurementCertificate, MeasurementDesign, certify_measurements
from .evaluation import SeparatedLimits, SeparatedResult, SeparatedStats, evaluate_separated
from .factor_width import FactorWidthAudit, audit_factor_width
from .taylor import Jet, TaylorLimits, TaylorResult, TaylorStats, restricted_taylor_sum, taylor_coefficients_separated
from .interpolation import HermiteDatum, HermiteLimits, HermiteResult, HermiteStats, ManualCountResult, HermiteOriginResult, OriginManualCountResult, interpolate_hermite, interpolate_origin_hermite, count_from_manual_designs, count_origin_from_manual_designs
from .parameters import PaperParameters, PaperAdmission, PaperParametersUnavailable, derive_paper_parameters, audit_paper_bounds, audit_bounded_cnf
from .sparsification import SparsificationLimits, SparsificationParameters, SparseLeaf, paper_sparsification_parameters, reference_sparsification_parameters, iter_disjoint_leaves
from .balance import BalanceLimits, BalancedSchedules, choose_balanced_schedules
from .preprocess import ReductionLimits, ParsimoniousReduction, reduce_width_occurrences, FreeVariableProjection, PreparedBoundedCNF, project_free_variables, prepare_bounded_cnf
from .construction import AuxiliaryDesign, ImplicitAuxiliaryDesign, ConstructedDesigns, ConstructionLimits, construct_auxiliary, construct_implicit_auxiliary, deterministic_schedules, construct_from_schedules, construct_bounded_designs, construct_paper_bounded_designs, count_from_constructed
from .backends import ArithmeticBackend, BackendUnavailableError
from .ganak import count_ganak
from .sudoku_adapter import from_sudoku_cnf, from_sudoku_puzzle

__all__ = ['CNFFormula', 'count_bruteforce', 'Polynomial', 'ReferenceLimits', 'ReplacementForm', 'ReplacementSystem', 'clause_satisfaction_polynomial', 'deformation_polynomial', 'CertifiedOccurrence', 'MeasurementCertificate', 'MeasurementDesign', 'certify_measurements', 'SeparatedLimits', 'SeparatedResult', 'SeparatedStats', 'evaluate_separated', 'FactorWidthAudit', 'audit_factor_width', 'Jet', 'TaylorLimits', 'TaylorResult', 'TaylorStats', 'restricted_taylor_sum', 'taylor_coefficients_separated', 'HermiteDatum', 'HermiteLimits', 'HermiteResult', 'HermiteStats', 'ManualCountResult', 'HermiteOriginResult', 'OriginManualCountResult', 'interpolate_hermite', 'interpolate_origin_hermite', 'count_from_manual_designs', 'count_origin_from_manual_designs', 'PaperParameters', 'PaperAdmission', 'PaperParametersUnavailable', 'derive_paper_parameters', 'audit_paper_bounds', 'audit_bounded_cnf', 'SparsificationLimits', 'SparsificationParameters', 'SparseLeaf', 'paper_sparsification_parameters', 'reference_sparsification_parameters', 'iter_disjoint_leaves', 'BalanceLimits', 'BalancedSchedules', 'choose_balanced_schedules', 'ReductionLimits', 'ParsimoniousReduction', 'reduce_width_occurrences', 'FreeVariableProjection', 'PreparedBoundedCNF', 'project_free_variables', 'prepare_bounded_cnf', 'AuxiliaryDesign', 'ImplicitAuxiliaryDesign', 'ConstructedDesigns', 'ConstructionLimits', 'construct_auxiliary', 'construct_implicit_auxiliary', 'deterministic_schedules', 'construct_from_schedules', 'construct_bounded_designs', 'construct_paper_bounded_designs', 'count_from_constructed', 'ArithmeticBackend', 'BackendUnavailableError', 'count_ganak', 'from_sudoku_cnf', 'from_sudoku_puzzle']
