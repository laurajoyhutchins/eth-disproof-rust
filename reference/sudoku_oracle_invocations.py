"""Source-correlated upper counts for original Sudoku vertex-oracle calls.

No algorithmic complexity conclusion follows from a finite event envelope.
The per-tree composition presumes the existing conditional paper fanout
bound includes *all potential child attempts*, including zero-certified
children that are not passed to ContractionEngine.contract.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from non_exponential_sudoku.contraction.packets import PacketEntry
from non_exponential_sudoku.core.network import Network
from non_exponential_sudoku.sudoku.input_oracles import (
    CellEntryOracle, UnitEntryOracle,
)
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.sudoku_oracle_cost import (
    CertifiedSudokuInput, certify_original_sudoku_oracles,
)


class UncertifiedOriginalOracleCalls(ValueError):
    """An inherited source oracle is not an identical, shape-correct root oracle."""


def _ceil_log2(value: int) -> int:
    if value < 1:
        raise ValueError("positive count required")
    return (value - 1).bit_length()


def _log2_sum_ceiling(exponents: tuple[int, ...]) -> int:
    """Never materialize the enormous powers in a symbolic full-tree bound."""
    if not exponents or any(type(v) is not int or v < 0 for v in exponents):
        raise ValueError("nonempty nonnegative logarithmic ceilings required")
    return max(exponents) + _ceil_log2(len(exponents))


@dataclass(frozen=True, slots=True)
class OriginalOracleInvocationEnvelope:
    """Conditional work on the original *not generated packet* oracles.

    A noncompiled elimination first makes dense input tables, and may
    subsequently fall back to direct() if an intermediate scope is too
    wide. We charge BOTH. Compiled leaf plans are no more expensive in
    original oracle calls. Optional zero-support is a separate input table
    pass made *before* a child contract, potentially on a pruned child.

    If potential_nodes_log2_ceiling is supplied, it must be the ceiling
    for the full *attempted* child tree, including pruned children, rather
    than only the number of actually executed recursion frames.
    """

    root_wires: int
    max_leaf_edges: int
    original_vertices: int
    max_cell_arity: int
    max_unit_arity: int
    leaf_strategy: Literal["enumerate", "eliminate"]
    zero_support: bool
    dense_factor_calls: int
    dense_factor_calls_log2_ceiling: int
    direct_per_node_log2_ceiling: int
    support_check_per_node_log2_ceiling: int
    per_potential_node_log2_ceiling: int
    potential_nodes_log2_ceiling: int | None
    all_potential_nodes_log2_ceiling: int | None
    max_original_entry_bit_work: int | None
    all_potential_nodes_bit_work_log2_ceiling: int | None
    proves_subexponential_totality: bool = False


def original_oracle_invocation_envelope(
    source: CertifiedSudokuInput, *,
    max_leaf_edges: int | None = None,
    leaf_strategy: Literal["enumerate", "eliminate"] = "eliminate",
    zero_support: bool = False,
    potential_nodes_log2_ceiling: int | None = None,
    extension_degree: int | None = None,
    precision: int | None = None,
) -> OriginalOracleInvocationEnvelope:
    """Bound the original input callback events per child attempt and tree.

    For every retained original vertex of root arity k:
    - direct() evaluates it at most 2**M times;
    - a Python elimination factor table evaluates it at most 2**k times;
    - the optional zero-support precheck evaluates it at most 2**k times.

    A failed uncompiled factor planner may perform the dense construction
    and *then* call direct(). The two counts must be added. Reused original
    callables retain exact arity and identity under both child constructors.
    No path enumerates an original input oracle inside PacketEntry.__call__.

    The potential-node composition depends on the separate paper fanout
    lemma and does not prove admissibility, resource nonrefusal, or closure
    of generated packet-oracle work.
    """
    if type(source) is not CertifiedSudokuInput:
        raise ValueError("certified canonical Sudoku source required")
    edges = source.wires if max_leaf_edges is None else max_leaf_edges
    if (type(edges) is not int or edges < 0
            or leaf_strategy not in ("eliminate", "enumerate")
            or type(zero_support) is not bool
            or (potential_nodes_log2_ceiling is not None and
                (type(potential_nodes_log2_ceiling) is not int
                 or potential_nodes_log2_ceiling < 0))):
        raise ValueError("invalid oracle invocation envelope configuration")
    if ((extension_degree is None) != (precision is None)
            or (extension_degree is not None and
                (type(extension_degree) is not int or extension_degree < 2))
            or (precision is not None and
                (type(precision) is not int or precision < 1))):
        raise ValueError("a complete canonical finite ring shape is required")

    cell_arity = 3 * source.digit_width
    unit_arity = source.side * source.digit_width
    # Exact finite number of rows for actual Sudoku source arities.
    table_calls = (source.cells * (1 << cell_arity) +
                   source.units * (1 << unit_arity))
    table_log = _ceil_log2(table_calls)
    direct_log = edges + _ceil_log2(source.vertices)
    support_log = table_log if zero_support else 0
    components = [direct_log]
    if leaf_strategy == "eliminate":
        components.append(table_log)
    if zero_support:
        components.append(support_log)
    per_node = _log2_sum_ceiling(tuple(components))
    total = (None if potential_nodes_log2_ceiling is None
             else per_node + potential_nodes_log2_ceiling)

    # The fixed original entry programs have local Boolean cost bounds,
    # and each makes exactly one ring.scalar(0/1) call in the eager Padic ABI.
    per_entry_work = None
    total_work = None
    if extension_degree is not None and precision is not None:
        scalar_work = 128 * (extension_degree * precision + 1)**2
        per_entry_work = (max(source.cell_work.boolean_bit_work_ceiling,
                              source.unit_work.boolean_bit_work_ceiling)
                          + scalar_work)
        if total is not None:
            total_work = total + _ceil_log2(per_entry_work)

    return OriginalOracleInvocationEnvelope(
        root_wires=source.wires,
        max_leaf_edges=edges,
        original_vertices=source.vertices,
        max_cell_arity=cell_arity,
        max_unit_arity=unit_arity,
        leaf_strategy=leaf_strategy,
        zero_support=zero_support,
        dense_factor_calls=table_calls,
        dense_factor_calls_log2_ceiling=table_log,
        direct_per_node_log2_ceiling=direct_log,
        support_check_per_node_log2_ceiling=support_log,
        per_potential_node_log2_ceiling=per_node,
        potential_nodes_log2_ceiling=potential_nodes_log2_ceiling,
        all_potential_nodes_log2_ceiling=total,
        max_original_entry_bit_work=per_entry_work,
        all_potential_nodes_bit_work_log2_ceiling=total_work,
    )


def audit_retained_original_oracles(
    puzzle: Puzzle, root: Network, descendant: Network,
) -> int:
    """Fail closed when source callbacks are forged, expanded, or duplicated.

    Exact identity and arity preservation are inherited from production
    make_child and CompiledChildPlan. Packet-entry callbacks are deliberately
    excluded from the original-oracle count and require separate bounds.
    """
    certify_original_sudoku_oracles(puzzle, root)
    descendant.validate()
    original = {
        id(vertex.oracle): (vertex.oracle, len(vertex.ports))
        for vertex in root.left + root.right
    }
    if len(original) != len(root.left) + len(root.right):
        raise UncertifiedOriginalOracleCalls("original oracle identity is not unique")
    encountered: set[int] = set()
    for vertex in descendant.left + descendant.right:
        oracle = vertex.oracle
        if isinstance(oracle, PacketEntry):
            continue
        key = id(oracle)
        if key not in original or original[key][0] is not oracle:
            raise UncertifiedOriginalOracleCalls("unknown original oracle identity")
        if key in encountered:
            raise UncertifiedOriginalOracleCalls("duplicated original oracle identity")
        if len(vertex.ports) != original[key][1]:
            raise UncertifiedOriginalOracleCalls("original oracle arity changed")
        encountered.add(key)
    return len(encountered)
