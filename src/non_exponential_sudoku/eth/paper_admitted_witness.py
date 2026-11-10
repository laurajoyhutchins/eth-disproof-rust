"""Paper Step-5 *symbolic* admission and a finite balancing-lemma witness.

No 2**lambda dimension, gigantic D=r**(2Q), or explicit huge formula is
ever constructed by virtual_unit_cnf_step5. Every 'proved' inequality is
either exact in small integers or follows from a documented conservative
upper bound on the logarithm of D; insufficient bounds are 'not_proved',
never silently treated as theorem admission.

This is a narrow source crosswalk, not a trace of the Lean BitProgram.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from math import isqrt
from typing import Literal

from .parameters import audit_paper_bounds


PAPER_COMMIT = "4eaee87548250b2682affda7d05d947c05554bae"
PAPER_PATH = (
    "preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/"
    "build/main_full_version.tex"
)
LEAN_PATH = "lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean"
LEAN_THEOREM = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_eth"
LEAN_SCOPE_PATH = "lean/docs/378.md"

Status = Literal["proved", "refuted", "not_proved"]


@dataclass(frozen=True, slots=True)
class PaperProofCheck:
    name: str
    status: Status
    reason: str


@dataclass(frozen=True, slots=True)
class VirtualUnitStep5Witness:
    """Sufficient admission certificate for F_n = AND_{i=1}^n x_i.

    Here n = 2**lambda_bits, M = n, and b = w = 1.
    The source formula is a mathematical *family*, not a materialized CNF.
    """

    lambda_bits: int
    nu_bits: int
    r: int
    Q: int
    R: int
    interval_start: int | None
    interval_end: int | None
    upper_log2_D: int
    variable_count_binary_bits: int
    D_expression: str
    n_description: str
    checks: tuple[PaperProofCheck, ...]
    exact_model_count: int = 1
    symbolic_M_equals_n: bool = True
    parameters_match_paper_step5: bool = True
    materialized_formula: bool = False
    executed_lean_machine: bool = False

    @property
    def admitted_by_sufficient_conditions(self) -> bool:
        return all(item.status == "proved" for item in self.checks)

    def check_status(self, name: str) -> Status:
        for entry in self.checks:
            if entry.name == name:
                return entry.status
        raise KeyError(name)


def virtual_unit_cnf_step5(
    lambda_bits: int, *, max_descriptor_bits: int = 256,
) -> VirtualUnitStep5Witness:
    """Certify the paper's sufficient Step-5 inequalities symbolically.

    Uses only integer arithmetic on lambda, Q, r, R. In particular it
    neither evaluates n=2**lambda nor D=r**(2Q), and never pretends
    conservative upper bounds are exact evaluations of D.
    """
    if type(lambda_bits) is not int or lambda_bits < 1:
        raise ValueError("lambda_bits must be a positive integer")
    if type(max_descriptor_bits) is not int or max_descriptor_bits < 1:
        raise ValueError("max_descriptor_bits must be a positive integer")
    if lambda_bits.bit_length() > max_descriptor_bits:
        raise ValueError("paper virtual dimension descriptor bit limit")
    lam = lambda_bits
    nu = (lam - 1).bit_length()
    r = isqrt(lam) // (nu * nu) if nu else 0
    Q = lam // (128 * nu) if nu else 0
    root = isqrt(lam)
    R = 4 * (root + int(root * root != lam))
    valid = r >= 2 and Q >= 1
    a0 = ((Q * (r - 1) - r * (R - 1)) // (2 * r)) if valid else None
    a1 = a0 + R - 1 if a0 is not None else None

    # r < 2**b, hence D=r**(2Q) < 2**(2Q*b).
    # The tests at lambda=2**34 are *sufficient* exact inequalities,
    # with no allocation of n, D or the polynomial interpolation ring.
    bit_upper = 2 * Q * r.bit_length() if valid else 0

    proofs: list[PaperProofCheck] = []

    def exact(name: str, condition: bool, reason: str) -> None:
        proofs.append(PaperProofCheck(
            name, "proved" if condition else "refuted", reason,
        ))

    def sufficient(name: str, is_proved: bool, reason: str) -> None:
        proofs.append(PaperProofCheck(
            name, "proved" if is_proved else "not_proved", reason,
        ))

    exact("n_positive", True, "n=2**lambda > 0")
    exact("paper_and_lean_n_at_least_20", lam >= 5,
          "n=2**lambda >= 32 > 20 for lambda>=5")
    exact("three_occurrences_and_width_three", True,
          "one unit occurrence per variable: b=w=1")
    exact("incidence_range", True, "M=n, hence n <= M <= 3n")
    exact("nonempty_factors", True, "M=n>0, b=w=1")
    exact("r_at_least_two", r >= 2, "literal Step-5 r=floor(sqrt(lambda)/nu**2)")
    exact("Q_at_least_one", Q >= 1, "literal Step-5 Q=floor(lambda/(128nu))")
    exact("R_at_least_32", R >= 32, "literal Step-5 R=4*ceil(sqrt(lambda))")
    exact("six_R_at_most_Q", Q >= 6 * R,
          "the manuscript's sufficient spectral interpolation interval regime")
    exact("spectral_interval_inside_0_to_Q",
          a0 is not None and a1 is not None and 0 <= a0 <= a1 <= Q,
          "exact integer spectral interval endpoints")
    sufficient("balancing_incidence_inequality",
               valid and 2 * bit_upper + (4).bit_length() <= lam,
               "4D**2 <= n by D < 2**upper_log2_D, b=w=1, M=n")
    sufficient("stronger_overview_12_D_squared_le_M",
               valid and 2 * bit_upper + (12).bit_length() <= lam,
               "the overview's stronger 12D**2 <= M condition")
    group_value = 2 * Q * r * r
    # x <= 2**lambda iff bit_length(x) <= lambda, or equality at
    # x==2**lambda. Recognize equality by its one-set-bit property,
    # never by materializing 2**lambda.
    group_pass = (
        group_value.bit_length() <= lam
        or (group_value.bit_length() == lam + 1
            and group_value > 0
            and group_value & (group_value - 1) == 0)
    )
    exact("balancing_groups_inequality", valid and group_pass,
          "2Qr**2 <= 2**lambda, exact comparison without constructing n")
    exact("spectral_tail_sufficient_inequality",
          valid and R * R >= 2048 * Q * nu,
          "integer sufficient binomial tail bound in paper Step 5")
    sufficient("dimension_at_most_2n_power_1_over_128",
               valid and 128 * bit_upper <= lam + 1,
               "D**128 <= 2n from conservative bit bound on r**(2Q)")
    sufficient("taylor_order_at_most_half_n",
               valid and Q >= 6 * R,
               "q=floor(3nR/Q); 6R<=Q implies 2q<=n")
    exact("hermite_unique_degree_3nR", valid,
          "Q*(floor(3nR/Q)+1)>3nR for defined paper parameters")

    return VirtualUnitStep5Witness(
        lambda_bits=lam, nu_bits=nu, r=r, Q=Q, R=R,
        interval_start=a0, interval_end=a1,
        upper_log2_D=bit_upper,
        variable_count_binary_bits=lam + 1,
        D_expression=f"{r}**{2 * Q}",
        n_description=f"2**{lam}",
        checks=tuple(proofs),
    )


@dataclass(frozen=True, slots=True)
class VirtualCoupledStep5Witness:
    """Symbolic, genuinely coupled three-occurrence/three-literal CNF family.

    For n=2**lambda, F_n=AND_i(x_i OR x_(i+1) OR x_(i+2)), indices
    cyclic modulo n. Every variable occurs in three distinct clauses and
    each clause has three distinct variables for n>=8, hence M=3n,
    b=w=3. No CNF, assignment, spectral tensor or huge integer n is
    allocated. No model count or intermediate rank is asserted.
    """

    lambda_bits: int
    n_description: str
    M_description: str
    r: int
    Q: int
    R: int
    checks: tuple[PaperProofCheck, ...]
    materialized_formula: bool = False
    executed_paper_algorithm: bool = False
    executed_lean_machine: bool = False

    @property
    def admitted_by_sufficient_conditions(self) -> bool:
        return all(check.status == "proved" for check in self.checks)

    def check_status(self, name: str) -> Status:
        for check in self.checks:
            if check.name == name:
                return check.status
        raise KeyError(name)


def virtual_coupled_3cnf_step5(
    lambda_bits: int, *, max_descriptor_bits: int = 256,
) -> VirtualCoupledStep5Witness:
    """Transfer the paper's *sufficient* checks to a coupled growing family.

    Reuses the already certified numeric Step-5 schedule without claiming
    the easy unit-clause family establishes an algorithm for a coupled CNF.

    For the cyclic triple-clause family, M=3n and b=w=3. Thus the
    incidence lemma's 2(b+w)D**2 <= M is exactly 4D**2 <= n,
    the original unit-clause certificate's condition. The overview's
    12D**2 <= M is the same condition too. All other source Step-5
    inequalities depend only on n,r,Q,R,D, not clause connectivity.
    This proof is also valid for any three-permutation incidence family
    with distinct literals and clauses, but does not certify its rank.
    """
    unit = virtual_unit_cnf_step5(
        lambda_bits, max_descriptor_bits=max_descriptor_bits,
    )
    base = {item.name: item for item in unit.checks}
    transferred: list[PaperProofCheck] = []
    for item in unit.checks:
        if item.name == "three_occurrences_and_width_three":
            transferred.append(PaperProofCheck(
                item.name, "proved" if lambda_bits >= 3 else "refuted",
                "n>=8: every cyclic 3-clause has three distinct literals; "
                "each variable occurs in exactly three clauses",
            ))
        elif item.name == "incidence_range":
            transferred.append(PaperProofCheck(
                item.name, "proved" if lambda_bits >= 3 else "refuted",
                "n>=8: normalized cyclic clauses are all distinct; M=3n",
            ))
        elif item.name == "nonempty_factors":
            transferred.append(PaperProofCheck(
                item.name, "proved" if lambda_bits >= 3 else "refuted",
                "n>=8: M=3n>0 and b=w=3",
            ))
        elif item.name == "balancing_incidence_inequality":
            transferred.append(PaperProofCheck(
                item.name, item.status,
                "for M=3n, b=w=3: 2(b+w)D**2<=M iff 4D**2<=n; "
                "same conservative upper bound as source-pinned unit witness",
            ))
        elif item.name == "stronger_overview_12_D_squared_le_M":
            transferred.append(PaperProofCheck(
                item.name, base["balancing_incidence_inequality"].status,
                "12D**2<=3n iff 4D**2<=n; same conservative proof",
            ))
        else:
            transferred.append(item)
    return VirtualCoupledStep5Witness(
        lambda_bits=unit.lambda_bits,
        n_description=unit.n_description,
        M_description=f"3*({unit.n_description})",
        r=unit.r, Q=unit.Q, R=unit.R,
        checks=tuple(transferred),
    )


@dataclass(frozen=True, slots=True)
class FiniteUnitBalanceWitness:
    """Fully enumerated incidence schedule satisfying Lemma incidence-labels.

    This uses zero-based labels corresponding to the manuscript's [r].
    It does not construct the giant occurrence-specific spectral tensor.
    """

    n: int
    M: int
    b: int
    w: int
    r: int
    Q: int
    D: int
    variable_schedules: tuple[tuple[int, int], ...]
    clause_schedules: tuple[tuple[int, int], ...]
    max_label_load: int
    max_variable_group: int
    balancing_lemma_hypotheses: bool
    balancing_lemma_conclusions: bool
    stronger_overview_balance_hypotheses: bool
    paper_step5_admitted: bool
    executed_full_spectral_construction: bool = False


def concrete_unit_balance_witness(n: int = 4096) -> FiniteUnitBalanceWitness:
    """Explicit, O(n) incidence labels for n independent positive unit clauses.

    For each v=e (zero based), a_v is the low two binary digits of v,
    and d_e is the next two digits. Thus every one of D=16 labels
    appears exactly n/16 times when 16 divides n.
    """
    if type(n) is not int or n < 3072 or n > 50_000 or n % 16:
        raise ValueError("finite unit witness requires 3072<=n<=50000, 16|n")
    r, Q, b, w = 2, 2, 1, 1
    D = r ** (2 * Q)
    variable = tuple(((v & 1), ((v >> 1) & 1)) for v in range(n))
    clauses = tuple((((v >> 2) & 1), ((v >> 3) & 1)) for v in range(n))
    loads = Counter(zip(variable, clauses))
    group_max = max(
        sum(labels[t] == group for labels in variable)
        for t in range(Q) for group in range(r)
    )
    max_load = max(loads.values(), default=0)
    hypotheses = (n <= n <= b * n
                  and 2 * (b + w) * D * D <= n
                  and 2 * Q * r * r <= n)
    conclusions = (
        len(loads) == D
        and max_load * D <= 2 * n
        and group_max * r <= 2 * n
    )
    stronger = 12 * D * D <= n and 2 * Q * r * r <= n
    if not (hypotheses and conclusions and stronger):
        raise ArithmeticError("explicit unit incidence schedule failed the paper lemma")
    return FiniteUnitBalanceWitness(
        n=n, M=n, b=b, w=w, r=r, Q=Q, D=D,
        variable_schedules=variable, clause_schedules=clauses,
        max_label_load=max_load, max_variable_group=group_max,
        balancing_lemma_hypotheses=hypotheses,
        balancing_lemma_conclusions=conclusions,
        stronger_overview_balance_hypotheses=stronger,
        paper_step5_admitted=audit_paper_bounds(n, n, b=1, w=1).admitted,
    )


@dataclass(frozen=True, slots=True)
class UnitCopyPartition:
    """Source-Step-4 copy decomposition, valid for unit clauses only.

    All deformed unit clause factors in a given copy read only variables
    from that copy. Concatenating copies as the Boolean variable ordering
    therefore gives a uniform exact TT rank upper bound 2**floor(D/2).
    This certifies an EXISTS representation, not its bit-time complexity.
    """

    copy_count: int
    max_copy_variables: int
    copy_blocks: tuple[tuple[int, ...], ...]
    variable_to_copy: tuple[int, ...]
    rank_upper_all_centers: int
    block_boundary_rank_upper: int = 1

    def taylor_coefficient_rank_upper(self, order: int) -> int:
        """Coefficient [z**j] has Q-matrix rank <= (j+1)*U."""
        if type(order) is not int or order < 0 or order > 1_000_000:
            raise ValueError("Taylor order outside bounded certificate range")
        return (order + 1) * self.rank_upper_all_centers


def unit_copy_partition(witness: FiniteUnitBalanceWitness) -> UnitCopyPartition:
    """Independently reproduce the paper's per-label copy allocation.

    The actual transfer in construction.construct_from_schedules assigns
    occurrence (e,v) to copy j equal to the number of *preceding*
    incidences with identical source label. With one occurrence for
    each variable, every variable has exactly one copy and labels
    cannot collide within a copy. Spectral coefficients only mix
    coordinates *inside* that copy.
    """
    if not isinstance(witness, FiniteUnitBalanceWitness):
        raise TypeError("expected a finite independent-unit-clause witness")
    if len(witness.variable_schedules) != witness.n or len(witness.clause_schedules) != witness.n:
        raise ValueError("unit schedule length mismatch")
    by_label: dict[tuple[tuple[int, int], ...], int] = {}
    groups: list[list[int]] = []
    labels_in_copy: list[set[tuple[tuple[int, int], ...]]] = []
    var_copies: list[int] = []
    for v in range(witness.n):
        label = tuple((
            witness.variable_schedules[v][t],
            witness.clause_schedules[v][t],
        ) for t in range(witness.Q))
        copy = by_label.get(label, 0)
        by_label[label] = copy + 1
        if copy == len(groups):
            groups.append([])
            labels_in_copy.append(set())
        if copy > len(groups) - 1 or label in labels_in_copy[copy]:
            raise ArithmeticError("non-unique variable/label assignment within auxiliary copy")
        labels_in_copy[copy].add(label)
        groups[copy].append(v)
        var_copies.append(copy)
    maximum = max(map(len, groups), default=0)
    if maximum > witness.D or max(by_label.values(), default=0) != len(groups):
        raise ArithmeticError("source-label copy capacity invariant failed")
    if sum(map(len, groups)) != witness.n:
        raise ArithmeticError("not every variable assigned to exactly one copy")
    return UnitCopyPartition(
        copy_count=len(groups),
        max_copy_variables=maximum,
        copy_blocks=tuple(tuple(group) for group in groups),
        variable_to_copy=tuple(var_copies),
        rank_upper_all_centers=1 << (maximum // 2),
    )
