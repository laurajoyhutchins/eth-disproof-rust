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
