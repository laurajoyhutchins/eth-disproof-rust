# One mode-assignment feasibility path

**Scope:** a behavior-preserving refactor of the Python reference mode paths. No theorem, native-kernel equivalence, or non-refusal claim follows from this change. The complete theorem acceptance test remains RED.

`core/mode_assignments.py` now owns the canonical multiplicity domains and the **single iterative prefix enumerator**. It enforces the same necessary rules at every call site:

1. Mode multiplicities start at zero, are bounded by both the mode's available rows and the precision/weight quotient, and have positive integer weights.
2. The sum of weighted multiplicities stays strictly below the current ring precision.
3. Only where an **actual paper PacketEntry** guarantees it, targeted occurrences at one `(target group, packet)` cannot exceed the number of distinct available target rows. Source-tile modes are not capped. This is the union of row sets, not a sum of counts.

The iterator supports scoped factors, arbitrary variable order, multiple target groups, bounded work accounting, and a finite number of yielded rows. It enumerates each accepted tuple exactly once in deterministic lexicographic order and uses an explicit stack/arrays instead of Python recursion. It does **not** automatically perform Hall matching or declare a feasible coefficient nonzero.

## Eliminated duplication

- `core.modes.weighted_tuples` remains an API-compatible thin wrapper for existing callers, but delegates its feasibility predicate to the shared iterator.
- `FactorBuilder.admissible_scoped_assignments` and `FactorBuilder.row_capped_assignments` were removed. `FactorBuilder.build` always uses the shared enumerator, with row constraints enabled only when the calling paper deformation enables them.
- Projected variable-elimination assignments use the **same weighted iterator without a target group**. A projected factor can combine multiple groups, and attaching one group's row constraint there would be unsound. The existing sparse-join weighted/degree checks remain necessary because new polynomial degrees arise after joins.
- The explicit mode sum uses the same iterator, with all active target-group caps only on the paper/Python packet path.
- `estimate_first_factor` uses the same iterator to bound *mandatory first-factor* child evaluations, instead of a separate weighted-partition DP. It enables row caps only for the same paper path. An exhausted preflight work allowance returns `unknown`, never a speculative capacity refusal.

`ModeBudget` retains the authoritative operation, child, state and estimated memory limits. Factor enumerations still charge traversal work; `max_states` refuses before exposing an over-limit assignment to the child evaluator. The optional Hall reference remains independent, so its work cannot silently replace the cheap necessary condition.

## Differential verification

Tests use an independent Cartesian-product reference on randomly generated mode scopes with overlapping rows, multiple packets/groups, zero-row modes and different weights. They also cover a 1,600-mode stack-independent case, cap boundaries, source-vs-target scopes, a first-factor preflight that counts **three** row-admissible assignments instead of **four** weight-admissible assignments, split factors, sparse/enumerating joins, and a real four-edge paper deformation against a separate exact oracle.

The full local checkpoint tier passed before publication. Optional native/backend tests skipped where their compiled dependencies were not installed. Strict mypy passed for all changed Python files.

## What this does not remove

Positive-weight checks in joins, precision-based valuation pruning in the mode catalog, and separate resource guards are still required. The Hall matching constraint is stronger but may cost more than the computation it saves. The mathematical worst-case support bound, input-oracle contracts, physical resources and the cell-parameter theorem are unchanged.
