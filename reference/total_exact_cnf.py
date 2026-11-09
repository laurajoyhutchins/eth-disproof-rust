"""Total exact #SAT factor elimination with a constructive bit-model ceiling.

This is a *separate, unconditional, exponentially bounded reference kernel*.
Its input ABI is already validated/canonical CNFFormula, not arbitrary
Python callback networks, and not the manuscript's recursive contraction.

No configured capacity cap or heuristic resource refusal occurs in this
reference. Finite hardware can of course exhaust physical resources;
mathematical totality refers to the finite explicit loops for every
finite CNF input.

Proof sketch for the reported worst-case reference-machine ceiling:

  1. Every factor represents counts over a DISJOINT set of already
     eliminated Boolean variables. Consequently each factor value and
     every intermediate product is an integer between 0 and 2**n.
  2. At most m+n+1 factor tables can coexist, each having at most 2**n
     entries. All masks and aggregate addresses fit in
     B=n+ceil_log2(m+n+3)+ceil_log2(w+2)+8 bits.
  3. Each initial clause table has <=2**n masks and <=w literal tests;
     each of n elimination stages scans at most m+n factors and
     enumerates <=2**n masks. Each factor index uses <=n bit tests.
     The bounded outer loops execute no more than
     256*2**n*(m+n+3)**2*(n+w+3)**2 modeled operations.
  4. A modeled word operation is implemented on a bit machine using
     <=64*(B+1)**2 bit steps. Schoolbook integer + and * with operands
     <=B bits satisfy this ceiling too. Multiply the bounds with slack:
     T <= 2**n * 2**16 * (m+n+3)**2
                     * (n+w+3)**2 * (B+1)**2.
  5. A generous bit-cell bound for live dense factors, scratch,
     selectors, input clause payload and descriptors is
     S <= 2**n * 2**12 * (m+n+3) * (n+w+B+5).

Each algorithmic loop charges an abstract-machine event, and every
large-integer + and * is also charged by actual operand size. The
recorded event-work is checked against the independent symbolic bounds.

These are complete bit-machine / bit-cell ceilings for the specified
*abstract reference algorithm*, not wall-clock, CPython machine
instructions, Python-object RSS, raw DIMACS parsing, or an asymptotic
bound for the paper's solver. They are exponential in n, deliberately.
"""
from __future__ import annotations

from dataclasses import dataclass

from non_exponential_sudoku.eth.cnf import CNFFormula


def _ceil_log2(x: int) -> int:
    if x < 1:
        raise ValueError("positive quantity required")
    return (x - 1).bit_length()


def _bits(x: int) -> int:
    return max(1, abs(x).bit_length())


@dataclass(frozen=True, slots=True)
class TotalReferenceEnvelope:
    variables: int
    clauses: int
    maximum_clause_width: int
    address_bits: int
    log2_work_upper: int
    log2_storage_upper: int
    # These are upper bounds of the form < 2**log2_..., including slack.


def total_reference_envelope(n: int, m: int, w: int) -> TotalReferenceEnvelope:
    """No 2**n allocation. Works even for astronomical symbolic n."""
    if any(type(x) is not int or x < 0 for x in (n, m, w)) or w > n:
        raise ValueError("require nonnegative n,m,w with w<=n")
    b = n + _ceil_log2(m + n + 3) + _ceil_log2(w + 2) + 8
    return TotalReferenceEnvelope(
        variables=n,
        clauses=m,
        maximum_clause_width=w,
        address_bits=b,
        log2_work_upper=(
            n + 16 + 2 * _ceil_log2(m + n + 3)
            + 2 * _ceil_log2(n + w + 3)
            + 2 * _ceil_log2(b + 1)
        ),
        log2_storage_upper=(
            n + 12 + _ceil_log2(m + n + 3)
            + _ceil_log2(n + w + b + 5)
        ),
    )


@dataclass(frozen=True, slots=True)
class TotalReferenceStats:
    events: int
    integer_adds: int
    integer_multiplies: int
    operand_aware_bit_steps: int
    maximum_integer_bits: int
    peak_live_table_entries: int
    peak_modelled_bit_cells: int
    log2_work_upper: int
    log2_storage_upper: int
    factor_eliminations: int
    clause_masks_tested: int
    bucket_masks_tested: int


@dataclass(frozen=True, slots=True)
class TotalReferenceResult:
    count: int
    stats: TotalReferenceStats


@dataclass(frozen=True, slots=True)
class _Dense:
    scope: tuple[int, ...]
    values: tuple[int, ...]


class _Count:
    def __init__(self, envelope: TotalReferenceEnvelope) -> None:
        self.bound = envelope
        self.events = 0
        self.adds = 0
        self.multiplies = 0
        self.bit_steps = 0
        self.max_bits = 1
        self.peak_entries = 0
        self.peak_memory = 0
        self.clause_masks = 0
        self.bucket_masks = 0
        self.eliminations = 0

    def step(self, count: int = 1) -> None:
        """One abstract RAM step expanded into an explicit bit-machine cap."""
        if count < 0:
            raise AssertionError("negative abstract work")
        self.events += count
        self.bit_steps += count * 64 * (self.bound.address_bits + 1) ** 2

    def _observe(self, *values: int) -> None:
        self.max_bits = max(self.max_bits, *(_bits(x) for x in values))
        if self.max_bits > self.bound.address_bits:
            raise AssertionError("source integer exceeded proved width")

    def add(self, a: int, b: int) -> int:
        self.adds += 1
        self._observe(a, b)
        self.step()
        self.bit_steps += 4 * (max(_bits(a), _bits(b)) + 1)
        result = a + b
        self._observe(result)
        return result

    def mul(self, a: int, b: int) -> int:
        self.multiplies += 1
        self._observe(a, b)
        self.step()
        self.bit_steps += 8 * (_bits(a) + 1) * (_bits(b) + 1)
        result = a * b
        self._observe(result)
        return result

    def storage(self, factors: list[_Dense], scratch: int = 0) -> None:
        entries = sum(len(f.values) for f in factors) + scratch
        self.peak_entries = max(self.peak_entries, entries)
        # Bit cells of values, address keys, factor metadata, input
        # clause literals, and temporary index/position arrays. This is
        # the abstract bit-string implementation, not Python object RSS.
        b, n, m, w = (self.bound.address_bits, self.bound.variables,
                      self.bound.clauses, self.bound.maximum_clause_width)
        cells = (
            entries * (n + b + 4)
            + (m + n + 3) * (n + b + 4)
            + m * w * (b + 1)
            + 16 * (n + b + 4) ** 2
        )
        self.peak_memory = max(self.peak_memory, cells)
        self.step(len(factors) + 1)

    def finalize(self, value: int) -> TotalReferenceResult:
        n = self.bound.variables
        if not 0 <= value <= (1 << n):
            raise AssertionError("count exceeds declared Boolean cube")
        if self.bit_steps.bit_length() > self.bound.log2_work_upper:
            raise AssertionError("source abstract work exceeds proved ceiling")
        if self.peak_memory.bit_length() > self.bound.log2_storage_upper:
            raise AssertionError("source abstract storage exceeds proved ceiling")
        return TotalReferenceResult(value, TotalReferenceStats(
            events=self.events,
            integer_adds=self.adds,
            integer_multiplies=self.multiplies,
            operand_aware_bit_steps=self.bit_steps,
            maximum_integer_bits=self.max_bits,
            peak_live_table_entries=self.peak_entries,
            peak_modelled_bit_cells=self.peak_memory,
            log2_work_upper=self.bound.log2_work_upper,
            log2_storage_upper=self.bound.log2_storage_upper,
            factor_eliminations=self.eliminations,
            clause_masks_tested=self.clause_masks,
            bucket_masks_tested=self.bucket_masks,
        ))


def count_total_reference(formula: CNFFormula) -> TotalReferenceResult:
    """Count all completions exactly, with no algorithmic resource refusal.

    Simple dense variable elimination uses deterministic variable order,
    explicit tuple/table indexing and ordinary nonnegative integers.
    A zero clause is preserved as a constant zero factor; unmentioned
    declared variables contribute their factor of two. No SAT oracle
    or approximate arithmetic is used by this function.
    """
    if not isinstance(formula, CNFFormula):
        raise TypeError("requires validated CNFFormula input")
    n, m = formula.nvars, len(formula.clauses)
    w = max((len(clause) for clause in formula.clauses), default=0)
    meter = _Count(total_reference_envelope(n, m, w))
    factors: list[_Dense] = []
    for clause in formula.clauses:
        # Produce a sorted unique scope without a hash table or sort.
        variables: list[int] = []
        for v in range(n):
            present = False
            for literal in clause:
                meter.step()
                if abs(literal) == v + 1:
                    present = True
            if present:
                variables.append(v)
        scope = tuple(variables)
        positions = [-1] * n
        meter.step(n)
        for j, v in enumerate(scope):
            positions[v] = j
            meter.step()
        table: list[int] = []
        for mask in range(1 << len(scope)):
            meter.clause_masks += 1
            meter.step()
            satisfied = False
            for literal in clause:
                meter.step()
                v = abs(literal) - 1
                bit = (mask >> positions[v]) & 1
                if bit == int(literal > 0):
                    satisfied = True
            table.append(int(satisfied))
            meter.step()
        factors.append(_Dense(scope, tuple(table)))
        meter.step()
        meter.storage(factors)

    scalar = 1
    for variable in range(n):
        meter.eliminations += 1
        attached: list[_Dense] = []
        detached: list[_Dense] = []
        union_mask = 0
        for factor in factors:
            contains = False
            for v in factor.scope:
                meter.step()
                if v == variable:
                    contains = True
            if contains:
                attached.append(factor)
                for v in factor.scope:
                    union_mask |= 1 << v
                    meter.step()
            else:
                detached.append(factor)
            meter.step()
        if not attached:
            scalar = meter.mul(scalar, 2)
            factors = detached
            meter.storage(factors)
            continue
        scope = tuple(v for v in range(n) if union_mask & (1 << v))
        meter.step(n)
        out_scope = tuple(v for v in scope if v != variable)
        meter.step(len(scope))
        positions = [-1] * n
        meter.step(n)
        for j, v in enumerate(scope):
            positions[v] = j
            meter.step()
        outputs = [0] * (1 << len(out_scope))
        meter.step(len(outputs))
        meter.storage(factors, scratch=len(outputs))
        for mask in range(1 << len(scope)):
            meter.bucket_masks += 1
            meter.step()
            product = 1
            for factor in attached:
                index = 0
                for j, v in enumerate(factor.scope):
                    bit = (mask >> positions[v]) & 1
                    if bit:
                        index |= 1 << j
                    meter.step()
                product = meter.mul(product, factor.values[index])
                meter.step()
            out_index = 0
            for j, v in enumerate(out_scope):
                bit = (mask >> positions[v]) & 1
                if bit:
                    out_index |= 1 << j
                meter.step()
            outputs[out_index] = meter.add(outputs[out_index], product)
            meter.step()
        if out_scope:
            detached.append(_Dense(out_scope, tuple(outputs)))
            meter.step()
        else:
            scalar = meter.mul(scalar, outputs[0])
        factors = detached
        meter.storage(factors)

    for factor in factors:
        if factor.scope:
            raise AssertionError("factor retains an uneliminated variable")
        scalar = meter.mul(scalar, factor.values[0])
    return meter.finalize(scalar)
