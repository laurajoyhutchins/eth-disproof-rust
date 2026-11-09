# Paper mode catalog and component planning: conditional cost closure

**Result:** Polynomial structural work for constructing one `mode_catalog` and one
`build_factorization_plan` when the paper packing/precision hypotheses hold.
This charges a formerly omitted term in `reference/whole_frame_recurrence.py`.
The full implementation is **not yet a non-refusing subexponential solver**.

Correspondence: `core/modes.py`, `contraction/children.py`,
`contraction/planning.py` and `contraction/engine.py`. The executable
reference is `reference/catalog_planning_work.py` with independent
`tests/unit/test_catalog_planning_work.py`.

## 1. Mode catalog source loops

At an eligible center with `i=v2(t)<u`, let `M` be parent edges, `V` its
vertices, `P` packets of `L=2^a` slots and `p` center precision. The paper's
packing bound supplies `P L <= 3M`, and the literal schedule has `a>=2u`.

The mode catalog builds its owner dictionaries by visiting exactly `2M`
ports. For each packet, it scans at most `L` slots twice. At most
`Y=2^(i+1)<=L` residue classes `y0` are visited. Each class scans at most
`L` column slots to produce its tile, at most `L` rows, and at most `L`
row valuations. It enumerates `b` in `[0,p-2]`, stopping earlier on
valuation or tile restrictions. Each emitted mode copies at most `L` tile
entries and `L` target-row indices and sums at most `L` tile-entry sizes.

Consequently:

\[
  m \le P\,2^{i+1}(p-1),\qquad
  W_{\mathrm{catalog}}=O\bigl((M+V+PL)^2+P\,2^{i+1}pL\bigr).
\]

The square is deliberately pessimistic: it covers dictionary collisions and
object bookkeeping rather than assuming constant-time hashing. Each
catalogue mode has a positive integer weight. The newer, valuation-pruned
`weight = a+1-v_max + b*(i+1-v_max)` has a strictly positive increment,
so it does not break the earlier one-mode-per-weight support argument.

The reference helper provides an interpreter-calibrated **sufficient estimated
`max_catalog_bytes` witness**: mode count times a linear-in-`L`
`getsizeof` majorant. The source deliberately excludes shared parent
geometry, integer objects and actual Python/native allocation from its own
guard; a guard witness is therefore **not** a peak-RSS proof. The helper
requires a positive estimate even if precision one emits no modes. A
separate real-audited four-slot packing checks actual modes, observed
`getsizeof` charges and guard non-refusal at several precisions.

## 2. Component planning source loops

`child_components` constructs a packet-to-edge map in `O(PL)` work, scans
at most `V` retained vertices and at most `2M` ports, and computes connected
components of a graph with at most `P+V` nodes and `2M` incidences.

**A concrete failure was found by TDD:** the former recursive disjoint-set
`find()` can raise `RecursionError` on a long bipartite path even when the
network, packet correspondence and child topology are valid. A path with
2,000 kept vertices on each side was enough to reproduce the failure in
the local baseline. The new implementation uses **iterative** root lookup,
path compression and **union by size**. Its parent-tree height is bounded by
`floor(log2(P+V))+1` even before path compression; each union and lookup is
finite without depending on the interpreter's call-stack limit.

The planner examines at most `r` occupied groups (`r=64` in the paper). It
can partition each group into at most `P+V` components, and each component
scans at most the group's incident mode indices to determine its own scope.
Including sorting, dictionary collision costs, comparisons and set creation,
a deliberately loose polynomial source-loop majorant is:

\[
  W_{\mathrm{plan}}=O\left(r\left[(M+V+PL+P+1)^3
    +(P+V+1)(m+1)(m+2)^2\right]\right).
\]

The existing component-count guard is satisfied, on these structural
premises, by `max_components >= r(P+V+1)`. This is a mathematical admission
budget and can still be far beyond physical memory.

The independent tests compare the produced components against graph BFS on
long paths and disconnected families, including
1,400 vertices per side. They also test the component-limit refusal,
whole-group fallback, split-factor scopes, and exact mode-to-factor scope
partitioning. The long path is a **valid incidence topology**, not a claim
that the particular padded synthetic packing meets all paper hypotheses.

## 3. Into the composed recurrence

The new symbolic helper forms an explicit conservative work model for the
catalog and plan and multiplies by a polynomial schoolbook bit-cost factor
for bounded integer/tuple/dictionary operations. Its result excludes any
unbounded input-oracle callback and actual CPython instruction counting.

The composed recurrence now charges a **fresh catalog and factor plan for
every interpolation sample at every center**, even when the implementation
caches both across samples. Thus no cache-hit assumption is needed for
worst-case accounting. Given the earlier paper path bounds
`M<=s`, `V<=s^O(1)`, `P L<=3M`, `L=s^o(1)`, and `p<=s^O(1)`, this term
requires polynomial bit work in the specified abstract model. It does not
change the asymptotic conditional `2^o(s)` composition.

## 4. Outstanding obligations, deliberately not green

- **Packing:** the source's full `balanced_labels` and `pack` implementation
  still needs end-to-end implementation-to-paper bit-work and memory
  correspondence; this lemma assumes a packing is already available.
- **Ordering and coefficients:** the mode elimination's arithmetic and
  ordering bit correspondence, native kernels, and all descendants' callback
  contracts remain separate. Source `modes.py` still refuses at finite
  catalogue-byte and optional count limits unless sufficient budgets are
  provisioned.
- **Totality:** the paper schedule may fail its numerical hypotheses and
  select terminal work. The terminal-leaf admission witness and the mode
  factor-budget witness remain **finite mathematical** resource functions,
  not physically available resources. Some source operations are still
  explicitly unbounded or not certified.
- **Parameter conversion:** network `s=Theta(N log N)` does not turn the
  conditional `2^o(s)` result into the desired `2^o(N)` in Sudoku cells.

Keep `research_acceptance/test_complete_bit_recurrence.py` **RED**. No theorem
claim follows from passing this TDD suite.
