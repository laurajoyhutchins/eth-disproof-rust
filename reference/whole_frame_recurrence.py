"""Compose paper contraction's *conditional* bit-work envelopes without hiding gaps.

The numeric result bounds only the explicitly charged components.  In
particular it is NOT an upper bound on the implemented solver, which has
arbitrary input callbacks, resource refusals and still-unproved glue costs.
An additional hypothetical polynomial-overhead model is deliberately named
and never accepted as a certified worst-case theorem.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import isqrt
from typing import Final

from non_exponential_sudoku.core.network import Network
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.sudoku_oracle_cost import (
    CertifiedSudokuInput, UncertifiedSudokuInput, certify_original_sudoku_oracles,
    original_oracle_bit_work_per_pass,
)
from reference.sudoku_oracle_invocations import (
    OriginalOracleInvocationEnvelope, original_oracle_invocation_envelope,
)

from non_exponential_sudoku.contraction.engine import paper_schedule_parameters
from reference.catalog_planning_work import catalog_planning_work
from non_exponential_sudoku.runtime.config import ContractorConfig
from reference.nested_ring_bit_cost import finite_shape_bit_envelope
from reference.oracle_lineage import paper_single_path_descriptor_bound
from reference.packet_preparation_work import cauchy_context_calls, prepared_child_work
from reference.precision_envelope import PaperFrameEnvelope, paper_frame_envelopes
from reference.recovery_bit_work import recovery_work


class UnclosedRecurrence(ValueError):
    """Do not turn a conditional count or arbitrary cost into a theorem."""


def ceil_log2(value: int) -> int:
    if type(value) is not int or value < 1:
        raise ValueError('positive integer required')
    return (value - 1).bit_length()


def ceil_sqrt(value: int) -> int:
    if type(value) is not int or value < 0:
        raise ValueError('nonnegative integer required')
    root = isqrt(value)
    return root + int(root * root < value)


def log2_sum_ceiling(*exponents: int) -> int:
    """Bound log2(sum_i 2**exponents[i]) without materializing powers."""
    if not exponents or any(type(x) is not int or x < 0 for x in exponents):
        raise ValueError('nonempty nonnegative integer exponents required')
    return max(exponents) + ceil_log2(len(exponents))


OPEN_PREMISES: Final[tuple[str, ...]] = (
    'input_oracle_bit_contract_and_uniform_metadata',
    'packing_planning_and_mode_ordering_bit_correspondence',
    'all_generated_entry_oracle_operations_and_native_policy',
    'early_numeric_fallback_covered_by_terminal_cost',
    'resource_limits_do_not_refuse_valid_inputs',
    'working_set_and_allocation_bit_accounting',
    'cell_count_parameter_conversion',
)


@dataclass(frozen=True, slots=True)
class FrameBudgetSkeleton:
    depth: int
    edges: int
    vertices: int
    terminal: bool
    center_count_ceiling: int
    sample_count_ceiling: int
    log2_weighted_support_ceiling: int
    log2_child_calls_ceiling: int
    log2_factor_ring_bit_work_ceiling: int
    log2_child_preparation_bit_work_ceiling: int
    log2_newton_interpolation_bit_work_ceiling: int
    log2_rational_recovery_bit_work_ceiling: int
    log2_named_local_work_ceiling: int
    # This is an abstract upper bound on number of binary assignments in a
    # fully-exhaustive leaf. It is not the cost of an uncapped implemented leaf.
    log2_exhaustive_leaf_assignments: int
    # Bounded source-level catalog and component-plan overhead, for all centers
    # and every interpolation sample (no assumption of cache hits).
    log2_catalog_planning_bit_work_ceiling: int = 0


@dataclass(frozen=True, slots=True)
class ConditionalPaperRecurrence:
    input_scale: int
    frames: tuple[FrameBudgetSkeleton, ...]
    log2_recursive_calls_ceiling: int
    # Product of per-depth child-call ceilings; not the total bit cost.
    log2_path_fanout_ceiling: int
    early_numeric_fallback_leaf_edge_ceiling: int
    max_single_path_oracle_descriptors: int
    max_single_path_oracle_name_bits: int
    # Optional verified original-input ABI, a ONE-PASS entry-cost ceiling.
    # Not a charge for the number of times a whole recursive frame invokes
    # those entries, and not a bound on generated PacketEntry callbacks.
    sudoku_original_oracle_per_pass_bit_work: int | None = None
    sudoku_original_oracle_scalar_calls_per_pass: int | None = None
    # One source-certified, POTENTIAL-child-tree event ceiling. It charges
    # fallback direct enumeration, factor-table construction and optional
    # zero-support separately. No generic PacketEntry work is included.
    sudoku_original_oracle_invocation_envelope: OriginalOracleInvocationEnvelope | None = None
    open_premises: tuple[str, ...] = OPEN_PREMISES

    def require_complete_theorem(self) -> None:
        """The current source has no non-refusing bit-time proof certificate."""
        raise UnclosedRecurrence('unproved premises: ' + ', '.join(self.open_premises))

    def hypothetical_polynomial_glue_log2_bound(self, *, degree: int) -> int:
        """Counterfactual: assume ALL missing local glue costs <= (s+1)**degree.

        Assume further that every leaf is actually evaluated, including the
        numeric-exception fallbacks, in time 2**M * polynomial(s).  The result
        is a CONDITIONAL arithmetic experiment, not a certified upper bound
        for the production code or a proof of non-refusal.
        """
        if type(degree) is not int or degree < 1:
            raise ValueError('positive polynomial degree required')
        polynomial_log = degree * ceil_log2(self.input_scale + 1)
        tail = self.frames[-1].log2_exhaustive_leaf_assignments
        tail = log2_sum_ceiling(tail + polynomial_log,
                                self.early_numeric_fallback_leaf_edge_ceiling + polynomial_log)
        # Every local operation outside recursive calls is charged via the
        # named terms or the explicit hypothetical polynomial allowance.
        for frame in reversed(self.frames[:-1]):
            local = log2_sum_ceiling(frame.log2_named_local_work_ceiling, polynomial_log)
            tail = log2_sum_ceiling(local, frame.log2_child_calls_ceiling + tail)
        return tail


def numeric_fallback_leaf_edge_ceiling(*, s: int, lambda_bits: int,
                                       maximum_slot_exponent: int,
                                       terminal_edges: int) -> int:
    """Upper bound for edges of a paper leaf under numeric-exception routes.

    Checks use M>=2*D**2*Delta, M>=L*D, 2*L<=Delta, where
    D=64**(2a), Delta=ceil(s**(9/10)), L=2**a.  The last inequality
    is automatic for paper-active lambda>=131072; Delta is bounded by
    2**ceil(9*lambda/10). If an M-inequality fails, its M is *less*
    than that threshold. Ordinary leaves also have M<=H=ceil(s/sqrt(lambda))
    or lie at the terminal depth; these are included explicitly.
    This does NOT remove the production leaf capacity refusal.
    """
    if (type(s) is not int or type(lambda_bits) is not int
            or type(maximum_slot_exponent) is not int
            or type(terminal_edges) is not int
            or s < 2 or lambda_bits < 131072 or maximum_slot_exponent < 2
            or terminal_edges < 0):
        raise ValueError('active paper parameters required')
    slots = 1 << maximum_slot_exponent
    dimension = 1 << (12 * maximum_slot_exponent)
    delta_upper = 1 << ((9 * lambda_bits + 9) // 10)
    delta_lower = 1 << ((9 * (lambda_bits - 1)) // 10)
    if 2 * slots > delta_lower:
        raise UnclosedRecurrence('2L<=Delta not certified from schedule')
    H = (s + isqrt(lambda_bits) - 1) // isqrt(lambda_bits)
    return min(s, max(H, 2 * dimension * dimension * delta_upper,
                      slots * dimension, terminal_edges))


def _active_frame(frame: PaperFrameEnvelope, config: ContractorConfig,
                  *, input_name_bits: int) -> FrameBudgetSkeleton:
    M, V, p, L = frame.edges, frame.vertices, frame.precision, frame.slots
    lam = max(1, (config.s - 1).bit_length())
    _, a, u, _ = paper_schedule_parameters(config.s, lam, frame.depth)
    if not (u >= 1 and a >= 2 * u and (1 << a) == L and M >= u):
        raise UnclosedRecurrence('paper schedule mismatch')
    P = 3 * M // L  # packing lemma's integer packet-count upper bound
    h = (3 * M + u - 1) // u
    precision = frame.child_precision
    E = M * (2 * L - 1) + 1
    centers = 2 * L - 1
    F = 64 * (V + P + 1)  # group or component factor count ceiling
    # Crucial center taper: K_i*p_i, not max_i(K_i)*max_i(p_i).
    color_precision = (P * (1 << u) * (p + 8 * M * (a + 1))
                       + 16 * P * h * L)
    alpha = 4 * ceil_sqrt(color_precision)
    k_max = P * L * (precision - 1)
    child_log = alpha + ceil_log2(centers * E * F)

    e = max(2, 4 * lam)
    ring = finite_shape_bit_envelope(e, precision)
    ring_bits = max(ring.add_bits, ring.mul_bits, ring.inv_bits,
                    ring.pow_bits(precision))
    # From center_evaluation_work.py: up to 64(k+1)(F+1)(p+1)^3
    # times 2^(2(alpha+1)) outer factor ring operations per sample.
    factor_ops = 64 * (k_max + 1) * (F + 1) * (precision + 1)**3
    factor_ring_log = (2 * (alpha + 1)
                       + ceil_log2(centers * E * factor_ops * ring_bits))

    # Charge a pessimistically fresh Cauchy context and an uncached child
    # preparation for *every possible* child. A real context is shared by
    # sibling children; its cache hits may only reduce these counts.
    prep = prepared_child_work(
        edges=M, vertices=V, packets=P, slots=L, modes=k_max,
        precision=precision, extension_degree=e,
        input_name_bits=input_name_bits,
    )
    context = cauchy_context_calls(L)
    context_work = (context.add * ring.add_bits + context.mul * ring.mul_bits
                    + context.inv * ring.inv_bits + context.pow * ring.pow_bits(precision)
                    + context.scalar * 128 * (ring.canonical_payload_bits + 1)**2)
    prep_log = child_log + ceil_log2(prep.schoolbook_bit_work_majorant + context_work + 1)

    # This counts all centers, and every interpolated point at each center.
    outer = (5 * E * (E + 1)) // 2 + E
    newton_ops = centers * (2 * outer + E)
    newton_log = ceil_log2(max(1, newton_ops) * ring_bits)

    recovery = recovery_work(M, L, u, p, extension_degree=e)
    recovery_bits = recovery.schoolbook_bit_work_majorant(e)
    recovery_log = ceil_log2(max(1, recovery_bits))
    # A center can rebuild its valuation catalog and factor plan when bounded
    # caches evict them. Charge a fresh copy per interpolation sample, even
    # though a reused plan normally needs much less work.
    catalog = catalog_planning_work(
        edges=M, vertices=V, packets=P, slots=L, groups=64,
        active_coordinates=u, center_valuation=u - 1,
        precision=precision, input_name_bits=input_name_bits,
    )
    catalog_log = ceil_log2(centers * E * catalog.schoolbook_bit_work_majorant)
    local_log = log2_sum_ceiling(factor_ring_log, prep_log,
                                  newton_log, recovery_log, catalog_log)
    return FrameBudgetSkeleton(
        frame.depth, M, V, False, centers, E, alpha,
        child_log, factor_ring_log, prep_log, newton_log, recovery_log,
        local_log, 0, log2_catalog_planning_bit_work_ceiling=catalog_log,
    )


def assemble_paper_recurrence(
    config: ContractorConfig, *, edges: int, vertices: int,
    input_name_bits: int,
    original_sudoku: tuple[Puzzle, Network] | None = None,
) -> ConditionalPaperRecurrence:
    """Join the named paper lemmas, retaining explicit unproved obligations.

    No configured capacity limit is used to bound recursive child calls.
    The mathematical positive-weight support bound is used instead.
    The frame-size envelope presumes valid packing and shrinkage; early
    numeric fallback must be charged via its separate leaf-edge ceiling.
    """
    if (not isinstance(config, ContractorConfig) or config.schedule != 'paper'
            or config.mode.strategy != 'eliminate'
            or config.mode.native_sparse or config.recursion.native_packet
            or config.recursion.native_leaf):
        raise UnclosedRecurrence('paper/Python elimination reference path required')
    if (any(type(x) is not int for x in (edges, vertices, input_name_bits))
            or edges < 0 or vertices < 0 or input_name_bits < 0
            or edges > config.s or config.precision > config.s
            or vertices > config.s * config.s
            or input_name_bits > config.s * config.s):
        raise UnclosedRecurrence('finite polynomial input shape required: M,p<=s; V,names<=s^2')
    # The source child constructor retains exact parent oracle references;
    # each nonempty packet creates one finite local PacketEntry. The paper
    # shrinkage check bounds the cumulative *single-path* descriptor count.
    # The previous model incorrectly reused only the root input-name size
    # when charging child preparation at every later depth.
    lineage = paper_single_path_descriptor_bound(
        root_edges=edges, root_vertices=vertices,
        root_input_name_bits=input_name_bits,
    )
    if lineage.max_visible_name_bits is None:
        raise UnclosedRecurrence('root input-name bit contract required')
    frames = paper_frame_envelopes(config, edges, vertices)
    original_work: int | None = None
    original_calls: int | None = None
    certificate: CertifiedSudokuInput | None = None
    largest_precision: int | None = None
    if original_sudoku is not None:
        if type(original_sudoku) is not tuple or len(original_sudoku) != 2:
            raise UnclosedRecurrence('original Sudoku requires puzzle and original Network')
        try:
            certificate = certify_original_sudoku_oracles(
                original_sudoku[0], original_sudoku[1],
            )
        except (UncertifiedSudokuInput, AssertionError) as exc:
            raise UnclosedRecurrence('uncertified original Sudoku oracle ABI') from exc
        if (certificate.wires != edges or certificate.vertices != vertices
                or certificate.root_name_bits > input_name_bits):
            raise UnclosedRecurrence('original Sudoku root shape/metadata mismatch')
        if config.precision < certificate.cells * certificate.digit_width + 1:
            raise UnclosedRecurrence('original Sudoku exact-count precision insufficient')
        lambda_bits = max(1, (config.s - 1).bit_length())
        extension_degree = max(2, 4 * lambda_bits)
        largest_precision = max(
            max(frame.precision, frame.child_precision) for frame in frames
        )
        original_work = original_oracle_bit_work_per_pass(
            certificate, extension_degree=extension_degree,
            precision=largest_precision,
        )
        original_calls = certificate.per_pass_scalar_calls
    if any(frame.vertices > lineage.max_vertices for frame in frames):
        raise UnclosedRecurrence('frame vertex envelope violates inherited oracle bound')
    # paper_frame_envelopes emits only potential active frames followed by
    # one terminal frame. Numeric packing failure is accounted separately.
    result: list[FrameBudgetSkeleton] = []
    for frame in frames:
        if frame.terminal:
            result.append(FrameBudgetSkeleton(
                frame.depth, frame.edges, frame.vertices, True,
                0, 0, 0, 0, 0, 0, 0, 0, 0, frame.edges,
            ))
        else:
            result.append(_active_frame(
                frame, config, input_name_bits=lineage.max_visible_name_bits,
            ))
    if not result[-1].terminal:
        raise UnclosedRecurrence('terminal frame required')
    count_log = 0
    fanout_log = 0
    for bounded_frame in reversed(result[:-1]):
        count_log = log2_sum_ceiling(0, bounded_frame.log2_child_calls_ceiling + count_log)
        fanout_log += bounded_frame.log2_child_calls_ceiling
    lam = max(1, (config.s - 1).bit_length())
    fallback = 0
    if result[0].terminal:
        fallback = result[0].edges
    else:
        max_a = max(paper_schedule_parameters(config.s, lam, f.depth)[1]
                    for f in result if not f.terminal)
        fallback = numeric_fallback_leaf_edge_ceiling(
            s=config.s, lambda_bits=lam, maximum_slot_exponent=max_a,
            terminal_edges=result[-1].edges,
        )
    invocation_envelope: OriginalOracleInvocationEnvelope | None = None
    if certificate is not None and largest_precision is not None:
        # The fanout model counts every potential attempted child, including
        # optional zero-support certificates that skip contract(). A single
        # attempt may pay for zero-support and, on a nonzero child, a leaf.
        invocation_envelope = original_oracle_invocation_envelope(
            certificate,
            max_leaf_edges=max(result[-1].edges, fallback),
            leaf_strategy=config.leaf.strategy,
            zero_support=config.recursion.zero_support.enabled,
            potential_nodes_log2_ceiling=count_log,
            extension_degree=max(2, 4 * lam),
            precision=largest_precision,
        )
    return ConditionalPaperRecurrence(
        config.s, tuple(result), count_log, fanout_log, fallback,
        lineage.max_vertices, lineage.max_visible_name_bits,
        original_work, original_calls, invocation_envelope,
    )
