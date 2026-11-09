# Terminal totality: remove an unnecessary edge cap, not the resource proof

**Status:** bounded improvement to the actual Python PAPER leaf executor.
The paper's complete worst-case, non-refusing algorithm remains **unproved in
this implementation**. This change does not make the abstract full contraction
run on arbitrarily large real hardware.

## Distinguish edge count from elimination width

`Network.direct(R, max_edges)` enumerates `2**M` Boolean edge assignments, so
its configured `max_edges` remains an explicit limit. Previously,
`eliminate_leaf(net, R, max_edges, ...)` refused all `M > max_edges`, **even
when every factor has width one and the elimination has constant width**.
That conflated the exponential reference's input size with the actual
elimination algorithm's intermediate width.

For the Python `eliminate_leaf` implementation:

- Allow `M > max_edges` **only when `max_factor_bytes` is specified**.
- Keep the initial factor width and all intermediate separator widths bounded
  by `max_width`; memory checks apply during both prepared-plan and dynamic
  execution.
- If the elimination would exceed the width bound, it still attempts the
  *existing* `Network.direct(R, max_edges)` path. That path **refuses before
  enumeration** when `M > max_edges`, rather than switching silently to an
  uncapped exhaustive algorithm.
- `LeafConfig(strategy='enumerate')` remains unchanged, and the default
  strategy remains enumeration. The Python elimination path is explicit.
- An explicitly requested native leaf continues to follow its own supported
  capacity contract. No native-versus-Python equivalence is presumed beyond
  existing tests.

The source's `max_factor_bytes` is a conservative **estimated factor-payload
budget**, not a measured process-RSS ceiling. Large input-oracle descriptions,
Python allocator overhead, and native representations are excluded.

## Conditional exact-work bound

Suppose the network has `M` edges and `V` vertices, every initial oracle has
arity at most `w`, and the actual greedy elimination order never creates a
factor scope with more than `w` surviving edges. Then:

- Vertex-entry evaluation requests at most `V * 2**w` oracle calls.
- There are exactly `M` variable-elimination steps. Each evaluates at most
  `2**w` output rows and two assignments to its eliminated edge.
- There are at most `V + M` live/temporary factor tables, so arithmetic work
  in elimination is at most `O(M * (V+M) * 2**w)` outer ring operations.
- Choosing the minimum-width variable and maintaining factor scopes adds a
  polynomial overhead in `M+V`. Every ring operation still requires its
  **separate bit-cost proof**, and oracle callbacks need explicit cost bounds.

For constant `w`, this is polynomial outer work even when `M` is larger than
the exhaustive cap. This statement applies **only if the width and factor
memory guards pass**, not to arbitrary generalized Sudoku instances.

## TDD

`tests/unit/test_large_low_width_terminal.py` exercises 19-, 48-, and
96-edge independent families with and without compiled leaf plans; a
connected 32-edge cycle; the literal paper engine's inactive schedule;
exhaustive-bound refusal on wide factors; refusal without a factor-memory
budget; and a too-small factor-memory budget. Exact counts are known
independently (`2**M`) and compared in a finite 2-adic ring with precision
`M+1`, so no modular wraparound can hide an incorrect answer.

The tests must never mark a capacity refusal as an exact Sudoku solution.
`research_acceptance/test_complete_bit_recurrence.py` remains red. A
non-refusing generalized-Sudoku theorem still requires a justified solution
for high-width leaves, source-oracle costs, all global resource limits,
and input-size conversion `s = Theta(N log N)`.
