"""Necessary packet-row restrictions on the literal paper mode expansion.

A targeted packet entry extracts a coefficient of a product with ONE
mode-variable choice per row. The resulting Hall matching condition is
necessary for its coefficient to be nonzero, independently of Cauchy values
or vertex-oracle callbacks. These conditions do not bound the full solver.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from math import isqrt
from collections.abc import Sequence

from non_exponential_sudoku.core.modes import Mode
from reference.global_mode_support import uniform_label_pair_paper_witness


def target_packet_row_caps(
    modes: Sequence[Mode], scope: Sequence[int], target_group: int,
) -> dict[int, int]:
    """Maximum total target occurrences allowed for each packet in a factor.

    This is the union of the rows mentioned by *targeted* modes, not the
    sum of each mode's row count. Source-group tile factors are excluded.
    """
    rows: dict[int, set[int]] = {}
    for index in scope:
        mode = modes[index]
        if mode.target == target_group:
            rows.setdefault(mode.packet, set()).update(mode.rows)
    return {packet: len(available) for packet, available in rows.items()}


def passes_packet_row_caps(
    modes: Sequence[Mode], scope: Sequence[int], beta: Sequence[int],
    target_group: int,
) -> bool:
    """Necessary, not sufficient, row-capacity test for one factor assignment."""
    if len(scope) != len(beta) or any(type(b) is not int or b < 0 for b in beta):
        raise ValueError('a nonnegative multiplicity is required per scoped mode')
    remaining = target_packet_row_caps(modes, scope, target_group)
    for index, count in zip(scope, beta):
        mode = modes[index]
        if mode.target == target_group:
            remaining[mode.packet] -= count
            if remaining[mode.packet] < 0:
                return False
    return True


def hall_packet_rows_possible(
    modes: Sequence[Mode], scope: Sequence[int], beta: Sequence[int],
    target_group: int, *, max_occurrences: int = 4000,
) -> bool:
    """Exact structural monomial-support test via unit-capacity matching.

    For each packet separately, match each mode occurrence to one distinct
    target row among that mode's `rows`. This is Hall's marriage criterion
    with repeated left vertices. It ignores arithmetic cancellation and so
    never proves a tensor coefficient nonzero. Large witnesses fail closed.
    """
    if max_occurrences < 1:
        raise ValueError('positive maximum occurrence count required')
    if not passes_packet_row_caps(modes, scope, beta, target_group):
        return False
    targeted_total = sum(count for index, count in zip(scope, beta)
                         if modes[index].target == target_group)
    if targeted_total > max_occurrences:
        raise ValueError('symbolic row matching needs a larger explicit work allowance')
    jobs_by_packet: dict[int, list[tuple[int, ...]]] = {}
    for index, count in zip(scope, beta):
        mode = modes[index]
        if mode.target == target_group:
            jobs_by_packet.setdefault(mode.packet, []).extend(
                [tuple(sorted(set(mode.rows)))] * count
            )
    if sum(map(len, jobs_by_packet.values())) > max_occurrences:
        raise ValueError('symbolic row matching needs a larger explicit work allowance')
    for jobs in jobs_by_packet.values():
        # Iterative augmenting paths, no reliance on Python recursion limit.
        owner: dict[int, int] = {}
        for new_job in range(len(jobs)):
            predecessors: dict[int, tuple[int, int]] = {}
            visited_jobs = {new_job}
            queue = [new_job]
            free_row: int | None = None
            scan = 0
            while scan < len(queue) and free_row is None:
                job = queue[scan]
                scan += 1
                for row in jobs[job]:
                    if row in predecessors:
                        continue
                    predecessors[row] = (job, row)
                    if row not in owner:
                        free_row = row
                        break
                    old_job = owner[row]
                    if old_job not in visited_jobs:
                        visited_jobs.add(old_job)
                        queue.append(old_job)
            if free_row is None:
                return False
            row = free_row
            while True:
                job, _ = predecessors[row]
                old_row = next((r for r, j in owner.items() if j == job), None)
                owner[row] = job
                if old_row is None:
                    break
                row = old_row
    return True


def brute_row_capped_assignments(
    modes: Sequence[Mode], precision: int, target_groups: Sequence[int],
    *, max_cartesian: int = 200_000,
) -> tuple[tuple[int, ...], ...]:
    """Independent, deliberately tiny oracle for all necessary row caps."""
    if type(precision) is not int or precision < 1:
        raise ValueError('positive precision required')
    limits = [min(len(mode.rows), (precision - 1) // mode.weight)
              for mode in modes]
    count = 1
    for limit in limits:
        count *= limit + 1
        if count > max_cartesian:
            raise ValueError('reference Cartesian search exceeds test allowance')
    return tuple(beta for beta in product(*(range(limit + 1) for limit in limits))
                 if sum(mode.weight * b for mode, b in zip(modes, beta)) < precision
                 and all(hall_packet_rows_possible(modes, range(len(modes)), beta, g)
                         for g in target_groups))


@dataclass(frozen=True, slots=True)
class UniformPaperRowCapacityWitness:
    """Formula-only, paper-admitted *structural* support witness.

    This lower-bounds assignments passing the weighted budget and all packet
    row Hall constraints. It does NOT prove their full factor values nonzero.
    """
    lambda_bits: int
    active_coordinate_count: int
    slots: int
    crossed_packets: int
    chosen_mode_exponents_per_packet: int
    subset_bits: int
    center_precision: int
    maximum_subset_weight: int
    per_packet_target_rows: int


def uniform_paper_row_capacity_witness(lambda_bits: int) -> UniformPaperRowCapacityWitness:
    """Exhibit 2**Omega(s/sqrt(log s)) geometrically *admissible* tuples.

    In the uniform full-label-pair packing, (r-1)/r of packets cross in
    coordinate zero. At t=1, one source-residue family in each such packet
    has modes b=1..B, weight a+1+b, and L/2 target rows. Select any
    subset, at multiplicity 0/1. With B=floor(L/(16*(sqrt(u)+1))) the
    largest possible total weight is strictly below the center precision.
    """
    if type(lambda_bits) is not int or lambda_bits < 131072 * 8:
        raise ValueError('symbolic paper witness requires u>=8')
    w = uniform_label_pair_paper_witness(lambda_bits)
    if not w.admitted_numeric_hypotheses:
        raise ValueError('uniform paper packing is not numerically admitted')
    s = w.edges
    u = lambda_bits // 131072
    a = 2 * u
    L = 1 << a
    Pcross = ((63 * s) // 64) // L
    B = L // (16 * (isqrt(u) + 1))
    if B < 1 or B > L // 2:
        raise ValueError('empty mode window or invalid row capacity')
    h = (3 * s + u - 1) // u
    pt = 1 + 8 * h * L + 8 * s * (a + 1)
    max_weight = Pcross * B * (a + 1 + B)
    if max_weight >= pt:
        raise ValueError('chosen subsets exceed the global weight budget')
    return UniformPaperRowCapacityWitness(
        lambda_bits, u, L, Pcross, B, Pcross * B, pt,
        max_weight, L // 2,
    )
