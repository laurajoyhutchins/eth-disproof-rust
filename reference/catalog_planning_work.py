"""Conditional polynomial work and guard budgets for paper catalog/planning.

This is source-level *abstract* integer/tuple/dictionary work, not CPython
instructions, process RSS, a proof of packing or a guarantee of admission.
The mode catalog is indexed by (packet, y0, b); planning partitions finite
child topology. Values fed to arbitrary vertex oracles are not evaluated here.
"""
from __future__ import annotations

from dataclasses import dataclass
from sys import getsizeof

from non_exponential_sudoku.core.modes import Mode


def _integer(value: int, *, lower: int = 0) -> int:
    if type(value) is not int or value < lower:
        raise ValueError(f"integer >= {lower} required")
    return value


def mode_owned_byte_ceiling(slots: int) -> int:
    """Conservative CPython getsizeof guard witness without allocating L tuples.

    The source charges a Mode, its instance dictionary, two coordinate tuples,
    each tile entry, and eight bytes. Tuple slot widths are calibrated from
    empty/singleton tuples, not assumed to be eight bytes across runtimes.
    A 4x base allowance covers different shared-key dictionary sizing.
    This is *not* a bound on actual retained RAM or arbitrary Python runtimes.
    """
    _integer(slots, lower=1)
    probe = Mode(0, 0, 0, 0, 1, 1, (), ())
    empty = getsizeof(())
    slot_bytes = max(1, getsizeof((0,)) - empty)
    base = getsizeof(probe) + getsizeof(probe.__dict__) + 2 * empty + 8
    per_slot = 2 * slot_bytes + getsizeof((0, 0))
    return 4 * (base + slots * per_slot)


@dataclass(frozen=True, slots=True)
class CatalogPlanningWork:
    """Sufficient finite guard witnesses and a polynomial loop-cost model."""

    edges: int
    vertices: int
    packets: int
    slots: int
    groups: int
    active_coordinates: int
    center_valuation: int
    precision: int
    y0_classes: int
    mode_count_ceiling: int
    component_count_ceiling: int
    catalog_guard_bytes: int
    catalog_outer_steps: int
    planning_outer_steps: int
    # Abstract bit-work majorant: elementary bounded integer/dict/list
    # operations using schoolbook arithmetic and worst-case hash collisions.
    schoolbook_bit_work_majorant: int

    @property
    def total_outer_steps(self) -> int:
        return self.catalog_outer_steps + self.planning_outer_steps

    @property
    def catalog_limit(self) -> int:
        return max(1, self.catalog_guard_bytes)

    @property
    def component_limit(self) -> int:
        return max(1, self.component_count_ceiling)


def catalog_planning_work(
    *, edges: int, vertices: int, packets: int, slots: int,
    groups: int, active_coordinates: int, center_valuation: int,
    precision: int, input_name_bits: int = 0,
) -> CatalogPlanningWork:
    """Charge a full catalog and a fresh factorization plan at one center.

    Required shape: valid paper-style packet accounting P*L<=3M,
    0<=i<u, a>=2u, r>=2. A separate packing proof must verify the
    geometric and shrinkage hypotheses, which this function cannot infer.

    The catalog's source work is dominated by P*2^(i+1)*L*p: each y0 scans
    <=L slots and every emitted b copies/scans <=L source/target entries.
    For planning, at most r groups independently rebuild <=P*L mappings,
    scan <=V vertices and <=2M ports, perform union/find on <=P+V nodes,
    and for each of <=P+V components scan <=m modes. The weighted iterative
    disjoint set has tree height <=log2(P+V+1), avoiding Python recursion.
    The broad polynomial envelope also covers sorting and adversarial dict
    collisions; it is not a precise CPython-instruction count.
    """
    M = _integer(edges)
    V = _integer(vertices)
    P = _integer(packets)
    L = _integer(slots, lower=1)
    r = _integer(groups, lower=2)
    u = _integer(active_coordinates, lower=1)
    i = _integer(center_valuation)
    p = _integer(precision, lower=1)
    names = _integer(input_name_bits)
    a = L.bit_length() - 1
    if L & (L - 1) or a < 2 * u or i >= u or M < u or P * L > 3 * M:
        raise ValueError('paper-style eligible center and packing bound required')
    Y = 1 << (i + 1)
    m = P * Y * max(0, p - 1)
    F = r * (P + V + 1)
    # Includes maps for all original edges and repeated scans/materialization.
    base = M + V + P * L + P + 1
    catalog = 64 * (base * base + P * Y * (p + 1) * (L + 1) + 1)
    # Every component scans at most m affected modes. A cubic outer ceiling
    # absorbs sorting, disjoint-set operations, tuple/dict work and collisions.
    planning = 128 * r * (base**3 + (P + V + 1) * (m + 1) * (m + 2)**2)
    max_records = base + m + F
    B = max(1, base.bit_length(), m.bit_length(), p.bit_length(), names)
    bit_work = 128 * (catalog + planning) * (max_records + 1) * (B + 1)**3
    return CatalogPlanningWork(
        M, V, P, L, r, u, i, p, Y, m, F,
        m * mode_owned_byte_ceiling(L), catalog, planning, bit_work,
    )
