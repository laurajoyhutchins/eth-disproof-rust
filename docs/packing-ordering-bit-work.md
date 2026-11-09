# Source-level packing and mode-ordering bit work

**Result:** conditional polynomial *nonrecursive* work for the actual `balanced_labels`, `pack`, `audit_packing`, and `select_variable` implementations. This closes two named source-loop accounting gaps in the **conditional** whole-frame recurrence. It does **not** establish that `balanced_labels` always satisfies the packing lemma or that the solver is total.

Executable companion: `reference/packing_ordering_work.py`. Independent tests: `tests/unit/test_packing_ordering_work.py`. The original `research_acceptance/test_complete_bit_recurrence.py` remains RED.

## 1. Label selection and packet materialization

Let the parent have `M` edges, `V` vertices, `r` groups and `a>=1` label coordinates; let `L=2**a`, and `R=r**a` be the full-label alphabet. The source creates integer labels with bit width `O(a log(r+1))`. **It never enumerates the entire alphabet**: when unused full labels exist, it chooses a fresh label in `O(a)` arithmetic, and otherwise searches among at most `V` occupied labels. Both left/right passes compare at most `V(V-1)/2` vertex pairs and scan at most `M` histogram entries per pair, with integer scores of polynomial bit width. Each pass also builds owner maps and degree histograms in `O(M+V)` structural visits.

`pack` creates at most `M` populated ordered label classes and at most `M` normalized symbol-pair families. The maximum class size is at most `M`, so the common padded height `Hpad=ceil(maximum/L)*L` satisfies `Hpad < M+L` for `M>0`. Every normalized family enumerates `L` orientations and at most `Hpad` candidate packet indices. Each packet allocates `L` slots and traverses at most `L` orientation-class indices. Thus even when all other packets are padded or discarded,

\[
P_{\mathrm{allocated}}\le M(M+L),\qquad
\mathrm{slot\ visits}\le M(M+L)L.
\]

`audit_packing` scans at most `M` owners, `P L` packet positions and `M a` coordinate/group incidences. These count **source operations before** checking the packer's quantitative theorem hypotheses. The receipt intentionally allows naive `O(n)` lookup costs for built-in hash-table collisions, rather than silently assuming expected-constant-time hashing.

`packing_source_work` combines these loops and bit widths into a loose degree-eight abstract schoolbook majorant in `M+V+L+2`, with polynomial factors for `a` and label-bit width. It assumes finite, bounded integer identifiers and schoolbook integer arithmetic. It does not bound CPython instructions, actual object headers, or the behavior of arbitrary vertex callbacks (which these routines do not evaluate).

## 2. Variable ordering

For at most `m` modes, at most `F` initial factors and per-mode multiplicity domain at most `p`, the exact `select_variable` routine makes at most `m` calls. Each call scans at most `F+m` factors; every factor scope contains at most `m` variables. Its adjacency, `min_fill` and `min_states` heuristics use nested loops and products over at most `m` modes.

The **numeric values** of ordering scores can be large: `output_states` and `joined_states` are products of at most `m` domain sizes, up to `p`. Their bit widths satisfy

\[
\operatorname{bits}(\mathrm{score})=O(m\log(p+1)+\log(m+1)).
\]

That does not allocate a factor table with that many states. Under a schoolbook integer and conservative set/dictionary model, `mode_ordering_work` bounds the complete ordering pass by a polynomial in `m`, `F`, and `log(p+1)`. Actual factor elimination is separately accounted by the support and convolution lemmas. Ordering heuristics are *not* assumed to find a narrow elimination width.

## 3. Composition and premise separation

For the paper path, `P L<=3M`, `L=O(s**(1/32768))`, `p<=s**O(1)`, `M,V<=s**O(1)`, and `m<=PL(p-1)`. Every quantity appearing above is polynomially bounded in `s`. The new whole-frame charge includes one packing pass **per active call** and a fresh elimination-ordering pass for **every interpolation sample at every eligible center**, without assuming cache reuse.

This supplies a conditional polynomial local overhead term; it does not change the earlier conditional `2**o(s)` exponent. In particular, it does not establish:

- that the actual greedy `balanced_labels` algorithm satisfies every paper packing and shrinkage hypothesis for all claimed inputs;
- that arbitrary input and generated oracles have uniformly bounded bit cost;
- that all capacity guards admit every input, or that physically available memory suffices;
- that network-edge `2**o(s)` implies `2**o(N)` for `N` Sudoku cells.

The GREEN tests cover finite actual networks, both tie-breaks, packet shapes, actual ordering calls and symbolic large dimensions. They test source correspondence and mathematical bounds but are **not a proof of universal behavior by finite sampling**. The theorem acceptance test remains RED.
