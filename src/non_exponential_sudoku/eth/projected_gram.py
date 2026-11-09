"""Exact projected Gram row space with a polynomial bit-work envelope.

For the actual restricted exceptional projector P, each rational entry
has denominator dividing 2**Q. For occupied labels L_v of an active
variable v, scale the Gram matrix by 2**Q:

    A[v,w] = sum_(a in L_v,b in L_w) 2**Q P[a,b] in Z.

The scaled matrix has k active rows and columns, k<=min(ell,group_size).
Its entries have B=Q+4+2 ceil_log2(ell+1) or fewer bits (ell is the
number of occupied labels in one copy and group). No D=r**(2Q)
matrix or exceptional eigenvector list is needed.

For integer A, the fraction-free Gauss-Jordan/Montante algorithm uses
exact Sylvester-identity divisions. Every stored intermediate is a
signed minor of A, including after row swaps and skipped zero columns.
Leibniz's bound gives at most

    B_minor = k*(B+ceil_log2(k+1))+4

bits per stored value. Each transient product/difference has <=
2*B_minor+4 bits; primitive normalized basis integers have <=B_minor
bits. Thus grade-school integer arithmetic plus Euclid has polynomial
bit complexity and polynomial *live* coefficient storage.

This establishes the projected-Gram/RREF STAGE only, under the
specified abstract integer bit machine. It does not certify the whole
transfer, balancing, label assignment, selector mode, interpolation,
recursion, or source capacity non-refusal. The symbolic work/storage
envelopes intentionally include broad slack for projector queries,
label indexing, integer elimination, and normalization. They do not
bound CPython interpreter instructions or object RSS.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Protocol

AuxiliaryLabel = tuple[tuple[int, int], ...]


class ProjectorOracle(Protocol):
    @property
    def r(self) -> int: ...

    @property
    def Q(self) -> int: ...

    @property
    def R(self) -> int: ...

    def exceptional_projector_at(
        self, source: AuxiliaryLabel, target: AuxiliaryLabel,
    ) -> Fraction: ...


def _ceil_log2_positive(x: int) -> int:
    if x < 1:
        raise ValueError("logarithm requires a positive integer")
    return (x - 1).bit_length()


def _bits(value: int) -> int:
    return max(1, abs(value).bit_length())


@dataclass(frozen=True, slots=True)
class ProjectedGramEnvelope:
    group_size: int
    occupied_labels: int
    active_variables: int
    r: int
    Q: int
    R: int
    gram_entry_bits_upper: int
    stored_minor_bits_upper: int
    transient_integer_bits_upper: int
    primitive_basis_bits_upper: int
    projector_query_count_upper: int
    integer_work_bit_steps_upper: int
    retained_abstract_bit_cells_upper: int


def projected_gram_envelope(
    *, group_size: int, occupied_labels: int, active_variables: int,
    r: int, Q: int, R: int,
) -> ProjectedGramEnvelope:
    """Allocation-free symbolic envelope for a single group and copy.

    Count every occupied label once. An auxiliary matrix is NOT an input.
    The ceilings are for grade-school bit operations and bit-string arrays.
    """
    values = (group_size, occupied_labels, active_variables, r, Q, R)
    if any(type(x) is not int for x in values):
        raise ValueError("Gram bound inputs must be exact integers")
    g, ell, k = group_size, occupied_labels, active_variables
    if (g < 0 or ell < 0 or k < 0 or k > min(g, ell) or r < 2
            or Q < 1 or not 1 <= R <= Q + 1):
        raise ValueError("invalid projected Gram dimensions or parameters")
    gram_bits = Q + 4 + 2 * _ceil_log2_positive(ell + 1)
    minor_bits = k * (gram_bits + _ceil_log2_positive(k + 1)) + 4
    temporary_bits = max(gram_bits, 2 * minor_bits + 4)
    address_bits = Q * (_ceil_log2_positive(r + 1) + 2) + 4
    # These explicitly polynomial, deliberately padded ceilings cover:
    #   <=ell**2 oracle requests with <=R*Q terms of size O(Q);
    #   <=k**3 exact Montante pivot operations;
    #   <=k**2 Euclidean gcd normalizations with <=O(B_minor)
    #   divisions each; and all group scans / label indexing.
    work = (1 << 20) * (
        (ell + 1) ** 2 * (Q + 1) ** 5 * (R + 1)
        * (address_bits + temporary_bits + 1) ** 3
        + (k + 1) ** 4 * (minor_bits + 1) ** 4
        + (g + ell + 1) ** 4 * (temporary_bits + 1) ** 2
    )
    # Input label payload, <=ell**2 cached queried projectors,
    # k*k Gram/RREF integer entries, one k-row scratch, and
    # k*g primitive-basis output. Shared aux.kernel is not owned here.
    storage = (1 << 12) * (
        (ell + 1) ** 2 * (Q * (_ceil_log2_positive(r + 1) + 2)
                         + Q + temporary_bits + 1)
        + (k + 1) ** 2 * (temporary_bits + 1)
        + (k + 1) * (g + 1) * (minor_bits + 1)
        + (ell + g + 1) * (address_bits + 1)
    )
    return ProjectedGramEnvelope(
        group_size=g, occupied_labels=ell, active_variables=k,
        r=r, Q=Q, R=R,
        gram_entry_bits_upper=gram_bits,
        stored_minor_bits_upper=minor_bits,
        transient_integer_bits_upper=temporary_bits,
        primitive_basis_bits_upper=minor_bits,
        projector_query_count_upper=ell * ell,
        integer_work_bit_steps_upper=work,
        retained_abstract_bit_cells_upper=storage,
    )


class _IntegerMeter:
    def __init__(self, ceiling: int) -> None:
        self.ceiling = ceiling
        self.bit_steps = 0
        self.max_bits = 1
        self.adds = 0
        self.products = 0
        self.exact_divisions = 0
        self.euclidean_divisions = 0

    def _observe(self, *values: int) -> None:
        for value in values:
            self.max_bits = max(self.max_bits, _bits(value))
        if self.max_bits > self.ceiling:
            raise ArithmeticError("projected Gram integer exceeds determinantal bound")

    def add(self, a: int, b: int) -> int:
        self._observe(a, b)
        self.adds += 1
        self.bit_steps += 4 * (max(_bits(a), _bits(b)) + 1)
        result = a + b
        self._observe(result)
        return result

    def sub(self, a: int, b: int) -> int:
        return self.add(a, -b)

    def mul(self, a: int, b: int) -> int:
        self._observe(a, b)
        self.products += 1
        self.bit_steps += 8 * (_bits(a) + 1) * (_bits(b) + 1)
        result = a * b
        self._observe(result)
        return result

    def div(self, a: int, b: int, *, euclid: bool = False) -> tuple[int, int]:
        if b == 0:
            raise ZeroDivisionError("zero divisor in fraction-free Gram")
        self._observe(a, b)
        self.bit_steps += 64 * (_bits(a) + 1) * (_bits(b) + 1)
        if euclid:
            self.euclidean_divisions += 1
        else:
            self.exact_divisions += 1
        quotient, remainder = divmod(a, b)
        self._observe(quotient, remainder)
        return quotient, remainder

    def divide_exactly(self, a: int, b: int) -> int:
        quotient, remainder = self.div(a, b)
        if remainder:
            raise ArithmeticError("Montante division was not exact")
        return quotient

    def gcd(self, a: int, b: int) -> int:
        a, b = abs(a), abs(b)
        while b:
            _, remainder = self.div(a, b, euclid=True)
            a, b = b, remainder
        return a


@dataclass(frozen=True, slots=True)
class ProjectedGramStats:
    envelope: ProjectedGramEnvelope
    exact_rank: int
    queried_projector_pairs: int
    cached_projector_pairs: int
    max_observed_integer_bits: int
    integer_bit_steps: int
    integer_additions: int
    integer_products: int
    integer_exact_divisions: int
    euclidean_divisions: int
    peak_matrix_entries: int


@dataclass(frozen=True, slots=True)
class ProjectedGramResult:
    rows: tuple[tuple[int, ...], ...]
    stats: ProjectedGramStats


def _fraction_free_basis(
    matrix: list[list[int]], meter: _IntegerMeter,
    stored_minor_bit_ceiling: int,
) -> tuple[tuple[int, ...], ...]:
    """Canonical primitive RREF rows, using only exact integer arithmetic.

    Invariants: all divisions are exact by Sylvester's determinant
    identity, and all stored updates are signed minors. The final
    row's pivot has a common signed determinant factor, so dividing
    its integer entries by their gcd yields the same primitive
    normalized row as rational RREF.
    """
    k = len(matrix)
    if not k:
        return ()
    if any(len(row) != k for row in matrix):
        raise ValueError("fraction-free Gram matrix must be square")
    a = [list(row) for row in matrix]
    previous_pivot = 1
    rank = 0
    pivots: list[int] = []
    for column in range(k):
        chosen = next((i for i in range(rank, k) if a[i][column]), None)
        if chosen is None:
            continue
        a[rank], a[chosen] = a[chosen], a[rank]
        pivot = a[rank][column]
        for i in range(k):
            if i == rank:
                continue
            factor = a[i][column]
            for j in range(k):
                if j == column:
                    continue
                numerator = meter.sub(
                    meter.mul(pivot, a[i][j]),
                    meter.mul(factor, a[rank][j]),
                )
                result = meter.divide_exactly(numerator, previous_pivot)
                if _bits(result) > stored_minor_bit_ceiling:
                    raise ArithmeticError("Montante minor bit bound violated")
                a[i][j] = result
            a[i][column] = 0
        previous_pivot = pivot
        pivots.append(column)
        rank += 1
        if rank == k:
            break

    out: list[tuple[int, ...]] = []
    for i in range(rank):
        divisor = 0
        for value in a[i]:
            divisor = meter.gcd(divisor, value)
        if divisor == 0:
            raise ArithmeticError("unexpected zero row after Gram elimination")
        row = [meter.divide_exactly(value, divisor) for value in a[i]]
        if row[pivots[i]] < 0:
            row = [-value for value in row]
        # Primitive integral rows need not have unit pivots, e.g. [2,1].
        if any(_bits(value) > stored_minor_bit_ceiling for value in row):
            raise ArithmeticError("primitive Gram basis bit bound violated")
        out.append(tuple(row))
    return tuple(out)


def projected_group_basis(
    auxiliary: ProjectorOracle,
    filled_copy: dict[AuxiliaryLabel, int],
    group: tuple[int, ...],
) -> ProjectedGramResult:
    """Return the source-equivalent projected measurement basis with proof data.

    Only the owned label copy and group are scanned. Never enumerate
    exception selectors or materialize any virtual D-coordinate array.
    """
    if len(set(group)) != len(group):
        raise ValueError("projected Gram group contains duplicate variables")
    positions = {v: i for i, v in enumerate(group)}
    labels_by_variable: dict[int, list[AuxiliaryLabel]] = {}
    for label, variable in filled_copy.items():
        if variable in positions:
            labels_by_variable.setdefault(variable, []).append(label)
    variables = tuple(v for v in group if v in labels_by_variable)
    occupied = sum(len(labels_by_variable[v]) for v in variables)
    k = len(variables)
    envelope = projected_gram_envelope(
        group_size=len(group), occupied_labels=occupied, active_variables=k,
        r=auxiliary.r, Q=auxiliary.Q, R=auxiliary.R,
    )
    meter = _IntegerMeter(envelope.transient_integer_bits_upper)
    projector_cache: dict[tuple[AuxiliaryLabel, AuxiliaryLabel], int] = {}
    scale = 1 << auxiliary.Q
    gram: list[list[int]] = []
    for v in variables:
        row: list[int] = []
        for w in variables:
            entry = 0
            for left in labels_by_variable[v]:
                for right in labels_by_variable[w]:
                    key = (left, right)
                    scaled = projector_cache.get(key)
                    if scaled is None:
                        value = auxiliary.exceptional_projector_at(left, right)
                        if scale % value.denominator:
                            raise ArithmeticError(
                                "exceptional projector denominator does not divide 2**Q"
                            )
                        scaled = meter.mul(value.numerator,
                                           scale // value.denominator)
                        projector_cache[key] = scaled
                    entry = meter.add(entry, scaled)
            if _bits(entry) > envelope.gram_entry_bits_upper:
                raise ArithmeticError("projected Gram entry bit bound violated")
            row.append(entry)
        gram.append(row)
    primitive = _fraction_free_basis(
        gram, meter, envelope.stored_minor_bits_upper,
    )
    rows = tuple(tuple(
        row[variables.index(v)] if v in labels_by_variable else 0
        for v in group
    ) for row in primitive)
    if len(projector_cache) > envelope.projector_query_count_upper:
        raise ArithmeticError("projector query count exceeds occupancy bound")
    if meter.bit_steps > envelope.integer_work_bit_steps_upper:
        raise ArithmeticError("projected Gram integer bit-work bound violated")
    return ProjectedGramResult(
        rows=rows,
        stats=ProjectedGramStats(
            envelope=envelope, exact_rank=len(rows),
            queried_projector_pairs=len(projector_cache),
            cached_projector_pairs=len(projector_cache),
            max_observed_integer_bits=meter.max_bits,
            integer_bit_steps=meter.bit_steps,
            integer_additions=meter.adds,
            integer_products=meter.products,
            integer_exact_divisions=meter.exact_divisions,
            euclidean_divisions=meter.euclidean_divisions,
            peak_matrix_entries=k * k,
        ),
    )


@dataclass(frozen=True, slots=True)
class ProjectedTransferGramEnvelope:
    """Conditional bound on ALL projected group/copy Gram calls.

    The condition is that the transferred schedules satisfy
    group_size*r<=2*n. This is the exact group-size inequality checked
    by construct_from_schedules, and one premise of the paper's
    admitted balancing construction. No claim about admission or
    the cost of producing these schedules is included.
    """

    variables: int
    occurrences: int
    possible_group_copy_calls_upper: int
    maximum_group_size_upper: int
    per_call: ProjectedGramEnvelope
    cumulative_abstract_bit_work_upper: int
    simultaneous_abstract_bit_storage_upper: int


def projected_transfer_gram_envelope(
    n: int, occurrences: int, *, r: int, Q: int, R: int,
) -> ProjectedTransferGramEnvelope:
    """Symbolic all-center Gram-stage ceiling, without a CNF or D allocation.

    In the source, there are Q centers, r groups per center, and at
    most ell nonempty occupied label copies. Each call returns at most
    k rows of width <=ceil(2*n/r). The retained-basis bound includes
    *all* groups and centers plus the scratch of one live Gram call,
    but excludes the independent replacement array, balancing
    potentials and full measurement-certificate computation.
    """
    if any(type(x) is not int for x in (n, occurrences, r, Q, R)):
        raise ValueError("transfer Gram bounds require exact integers")
    if n < r or occurrences < 0:
        raise ValueError("transfer bound requires n>=r and nonnegative incidences")
    group_size = (2 * n + r - 1) // r
    k = min(group_size, occurrences)
    local = projected_gram_envelope(
        group_size=group_size, occupied_labels=occurrences,
        active_variables=k, r=r, Q=Q, R=R,
    )
    calls = Q * r * occurrences
    # Address/tuple and per-row metadata bits are included conservatively.
    retained_basis = (
        calls * k * group_size
        * (local.primitive_basis_bits_upper + Q * (r.bit_length() + 2) + 8)
    )
    return ProjectedTransferGramEnvelope(
        variables=n, occurrences=occurrences,
        possible_group_copy_calls_upper=calls,
        maximum_group_size_upper=group_size,
        per_call=local,
        cumulative_abstract_bit_work_upper=(
            calls * local.integer_work_bit_steps_upper),
        simultaneous_abstract_bit_storage_upper=(
            local.retained_abstract_bit_cells_upper + retained_basis),
    )
