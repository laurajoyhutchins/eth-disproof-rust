"""Finite sufficient resource budgets, not a total/subexponential solver theorem.

Two independent results:
  * Every validated finite tensor network with total finite-ring oracles has a
    resource-non-refusing *mathematical* terminal factor elimination when the
    width is M and the factor budget covers (V+M+2)*2**M entries. Materializing
    this budget may require astronomical memory and host execution can fail.
  * For a finite positive-weight ModeEliminator with already prepared modes,
    an exact global support count A yields conservative guard budgets. This
    does NOT cover mode_catalog allocation, packing, unknown oracle bodies,
    Python/native memory or recursive child calls after they are dispatched.

Both witnesses keep the input size parameter and physical admission separate.
"""
from __future__ import annotations

from dataclasses import dataclass
from collections.abc import Sequence

from non_exponential_sudoku.core.modes import Mode
from non_exponential_sudoku.core.network import Network, TensorRing, estimated_coefficient_bytes
from non_exponential_sudoku.runtime.config import LeafConfig, ModeLimits


class BudgetNotMaterializable(ValueError):
    """Symbolic sufficient budget is not intended to be allocated here."""


def ceil_log2_positive(value: int) -> int:
    if type(value) is not int or value < 1:
        raise ValueError('positive exact integer required')
    return (value - 1).bit_length()


@dataclass(frozen=True, slots=True)
class TerminalBudgetWitness:
    """Sufficient terminal factor-budget shape for total finite oracles.

    Does not bound peak Python RSS; factor data and all oracle bodies must
    terminate. A finite symbolic witness is not a physical resource grant.
    """

    edges: int
    vertices: int
    max_width: int
    entries_log2_ceiling: int
    estimated_bytes_log2_ceiling: int
    bytes_per_coefficient: int

    def to_leaf_config(self, *, max_exhaustive_bits: int = 24) -> LeafConfig:
        """Only materialize a small configured sufficient budget by opt-in.

        We use edge limit M, width M, and a large enough factor-byte budget
        to eliminate without invoking the exhaustive fallback. This config
        will still have other possible failures (non-total user callbacks,
        host memory exhaustion), which this arithmetic cannot eliminate.
        """
        if type(max_exhaustive_bits) is not int or max_exhaustive_bits < 1:
            raise ValueError('positive materialization exponent required')
        if self.edges > max_exhaustive_bits:
            raise BudgetNotMaterializable('symbolic terminal budget is too large to allocate')
        entries = (self.vertices + self.edges + 2) << self.edges
        return LeafConfig(
            strategy='eliminate', limit=max(1, self.edges),
            max_width=max(1, self.edges), lookup_entries=0,
            max_factor_bytes=max(1, entries * self.bytes_per_coefficient),
        )


def terminal_budget(net: Network, ring: TensorRing) -> TerminalBudgetWitness:
    """Bound the *implemented* leaf table memory guard on any valid topology.

    Every live/intermediate factor table has at most 2**M rows and at most
    V+M+1 simultaneous tables (initial vertex factors plus one per edge
    elimination); the +2 allowance includes the output table and constants.
    Guard estimates use estimated_coefficient_bytes(ring), as production does.
    The method checks topology but cannot inspect/ certify arbitrary oracles.
    """
    net.validate()
    return symbolic_terminal_budget(
        edges=net.edges, vertices=len(net.left) + len(net.right),
        bytes_per_coefficient=estimated_coefficient_bytes(ring),
    )


def symbolic_terminal_budget(*, edges: int, vertices: int,
                             bytes_per_coefficient: int) -> TerminalBudgetWitness:
    """Work with huge terminal edge bounds without allocating 2**edges bits.

    This is an upper logarithmic *resource requirement*. It does not create
    factor tables, coefficient rings, or a Python int with 2**edges digits.
    """
    if (any(type(x) is not int for x in (edges, vertices, bytes_per_coefficient))
            or edges < 0 or vertices < 0 or bytes_per_coefficient < 1):
        raise ValueError('finite nonnegative shape and positive coefficient bytes required')
    entries_log = edges + ceil_log2_positive(vertices + edges + 2)
    byte_log = entries_log + ceil_log2_positive(bytes_per_coefficient)
    return TerminalBudgetWitness(edges, vertices, max(1, edges), entries_log,
                                 byte_log, bytes_per_coefficient)


def exact_weighted_support(modes: Sequence[Mode], precision: int) -> int:
    """Finite exact support count using degree DP (no Cartesian enumeration).

    For source-generated modes: positive integer weights and nonnegative
    finite row caps. Pseudopolynomial in precision; use symbolic bounds for
    astronomical paper-scale p instead of calling this helper.
    """
    if type(precision) is not int or precision < 1:
        raise ValueError('positive integer precision required')
    counts = [1] + [0] * (precision - 1)
    for mode in modes:
        if type(mode.weight) is not int or mode.weight < 1:
            raise ValueError('positive integer mode weights required')
        cap = min(len(mode.rows), (precision - 1) // mode.weight)
        next_counts = [0] * precision
        for degree, count in enumerate(counts):
            if not count:
                continue
            for beta in range(min(cap, (precision - 1 - degree) // mode.weight) + 1):
                next_counts[degree + mode.weight * beta] += count
        counts = next_counts
    return sum(counts)


@dataclass(frozen=True, slots=True)
class ModeBudgetWitness:
    """Sufficient ModeBudget guard ceilings for preconstructed local factors.

    Preconditions: fixed positive-weight mode catalog, already bounded
    finite-ring coefficient values, total child-evaluation callback, at most
    F factors initially, and no source code path outside ModeEliminator.
    """

    modes: int
    factors: int
    precision: int
    admissible_assignments: int
    bytes_per_coefficient: int
    limits: ModeLimits


def finite_mode_budget(modes: Sequence[Mode], *, factors: int,
                       precision: int, bytes_per_coefficient: int) -> ModeBudgetWitness:
    """Overbudget ModeEliminator's guards without claiming runnable capacity.

    Let A be the global positive-weight domain count and m,F,p the number
    of modes, starting factors, and precision. Each partial factor table has
    at most A rows and p coefficients per row. There are at most F+m live
    factor tables. For the Python sparse/enumerate algorithms every join
    sees at most A**2 row pairs; each polynomial convolution <=p**2 pairs.

    Operation budget is intentionally loose and includes degree-prefix DP,
    ordering scans, all projection loops, final convolution and joins.
    It is NOT a bit-operation or Python allocation bound.
    """
    if type(factors) is not int or factors < 1 or type(bytes_per_coefficient) is not int or bytes_per_coefficient < 1:
        raise ValueError('positive factor count and coefficient-byte estimate required')
    A = exact_weighted_support(modes, precision)
    m, F, p = len(modes), factors, precision
    # ModeBudget can have at most F+m live tables (no nested factor joins
    # remain in its factor list). +1 allows a table being constructed.
    retained_tables = F + m + 1
    state_ceiling = retained_tables * A
    term_ceiling = state_ceiling * p
    byte_ceiling = term_ceiling * bytes_per_coefficient + 128 * state_ceiling
    # Every initial factor and every projected factor can contain at most A
    # assignments and each polynomial has at most p coefficients. This bound
    # also dwarfs the order_work and table-building DP counters.
    op_ceiling = (256 * (m + 1)**3 * (F + 1)**3 * (p + 1)**4 * (A + 1)**2)
    limits = ModeLimits(
        max_components=max(1, F),
        max_factor_states=max(1, A),
        max_live_terms=max(1, term_ceiling),
        max_operations=max(1, op_ceiling),
        max_child_contractions=max(1, F * A),
        max_estimated_bytes=max(1, byte_ceiling),
    )
    return ModeBudgetWitness(m, F, p, A, bytes_per_coefficient, limits)


@dataclass(frozen=True, slots=True)
class SymbolicModeBudget:
    """Logarithmic sufficient ModeBudget shape for global support <=2**alpha.

    Only structural guard ceilings; materialization with astronomical alpha
    would itself be unreasonable and does not establish physical totality.
    """
    modes: int
    factors: int
    precision: int
    support_exponent: int
    coefficient_bytes: int
    max_factor_states_log2: int
    max_live_terms_log2: int
    max_operations_log2: int
    max_child_contractions_log2: int
    max_estimated_bytes_log2: int

    def materialize(self, *, max_support_exponent: int = 16) -> ModeLimits:
        if (type(max_support_exponent) is not int or max_support_exponent < 0):
            raise ValueError('invalid materialization exponent')
        if self.support_exponent > max_support_exponent:
            raise BudgetNotMaterializable('global mode-support ceiling is symbolic only')
        A = 1 << self.support_exponent
        m, F, p = self.modes, self.factors, self.precision
        tables = F + m + 1
        states = tables * A
        return ModeLimits(
            max_components=F, max_factor_states=A,
            max_live_terms=states*p,
            max_operations=256*(m+1)**3*(F+1)**3*(p+1)**4*(A+1)**2,
            max_child_contractions=F*A,
            max_estimated_bytes=states*(p*self.coefficient_bytes + 128),
        )


def symbolic_mode_budget(*, modes: int, factors: int, precision: int,
                         support_exponent: int,
                         bytes_per_coefficient: int) -> SymbolicModeBudget:
    """Bound paper-mode guards in logarithmic size without generating states.

    Requires a proved positive-weight support upper bound A<=2**alpha.
    For a real paper frame, the previous colored-partition argument supplies
    alpha; this helper does not verify paper packing or source semantics.
    """
    if (any(type(x) is not int for x in (
        modes, factors, precision, support_exponent, bytes_per_coefficient))
            or modes < 0 or factors < 1 or precision < 1
            or support_exponent < 0 or bytes_per_coefficient < 1):
        raise ValueError('valid nonnegative paper-mode shape required')
    m, F, p, a, bpc = modes, factors, precision, support_exponent, bytes_per_coefficient
    tables = F + m + 1
    return SymbolicModeBudget(
        m, F, p, a, bpc,
        max_factor_states_log2=a,
        max_live_terms_log2=a + ceil_log2_positive(tables * p),
        # (2**alpha+1)**2 <= 2**(2alpha+2)
        max_operations_log2=(2*a + 2 + ceil_log2_positive(
            256 * (m+1)**3 * (F+1)**3 * (p+1)**4)),
        max_child_contractions_log2=a + ceil_log2_positive(F),
        max_estimated_bytes_log2=a + ceil_log2_positive(tables * (p*bpc + 128)),
    )
