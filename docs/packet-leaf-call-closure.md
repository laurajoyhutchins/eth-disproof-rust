# Generated packet-entry calls: source-level closure and limits

**Status:** conditional *outer ring-method call* bounds for the eager
Python `PacketEntry` implementation, both on actual instantiated children
and symbolically over potential children of the literal paper schedule.
They are **not** elementary bit-operation bounds or a proof of a practical
non-exponential Sudoku algorithm.

## One instantiated descendant leaf

`reference/packet_leaf_work.py` combines the existing
`packet_evaluation_envelope(entry)` with the actual call sites:

- `Network.direct`: for a child with `M` wires, any packet entry can be
  called at most `2**M` times.
- `eliminate_leaf`: for an entry with `k` incident wires, its input
  factor table requires at most `2**k` calls. The uncompiled evaluator
  can prepare tables **and then** fall back to `direct`; both terms are
  included.
- `certify_zero`: uses `_packet_may_be_nonzero`, a structural
  overapproximation, **not** `PacketEntry.__call__`. Its visits are
  recorded separately and do not falsely inflate packet ring operations.

For an instantiated graph with packet entries `Q`, a pessimistic
per-leaf packet callback bound is

\[
A_{\text{packet}}\le\sum_{v\in Q}
\left(2^M+\mathbf 1_{\rm eliminate}2^{\deg(v)}\right).
\]

For each `v`, its existing source-based local ring-call bound `B_v`
is multiplied by the same invocation count. The evaluator has an optional
precision lift from its **creation ring** to the caller's ring; the new
certificate also charges scalar-coordinate mask visits for that lift.

The checker requires the instantiated packet's port indices to match its
geometry, and rejects native, lazy or incompatible precision-lift paths
rather than assigning them zero cost. It never assumes that the arbitrary
*other* vertex callbacks are inexpensive. Tests count actual packet
callbacks, ring-method invocations and lift masks, including a descendant
that inherits a packet entry created in a prior recursive generation.

## Symbolic paper-schedule envelope

Let `L` be an active packet's slot count and `p` its local precision.
The real paper mode catalog creates at most

\[
K=L(p-1)
\]

modes **per packet**. A packet evaluator has at most `L` rows,
`L` right terms per row, `K` target contributions per row, and
`K` source tiles with at most `L` terms each.

After `j` rows, any exponent-key vector has nonnegative coordinates and
coordinate sum at most `j`. The existing
`paper_mode_reachability.py` lemma therefore gives at most
`(K+1)^L` keys at any time, without requiring their enumeration.

Bounding every transition of the **actual** eager Python
`_evaluate_python` loops yields the deliberately loose upper bound

\[
B(L,p)=64(L+1)^2(K+1)^{L+1}
\]

on **outer** `add/sub/neg/mul/scalar/pow` calls per prepared packet
entry evaluation. The bound includes both the zero-target and
nonzero-target cases, but excludes the primitive bit work hidden *inside*
each call, `j**mode.b` integer construction, dictionary hashing,
coefficient preparation, lift bit costs, native and lazy paths.

`reference/paper_packet_calls.py` returns
`ceil(log2(B))` without allocating `(K+1)^L`, then uses the existing
conditional single-path oracle-lineage ceiling
`V_0+floor(32M_0/29)` and the paper potential-node fanout bound.
With `M_*` bounding terminal and numeric-fallback leaf edges and
`C` potential nodes, the resulting pessimistic full-tree count is

\[
\#\text{outer ring calls}
\le
C\;2^{M_*+1}
\bigl(V_0+\lfloor32M_0/29\rfloor\bigr)
\;B(L_{\max},p_{\max}).
\]

The factor `2` accounts for prebuilt input factor tables **plus**
the exhaustive fallback. Optional zero-support attempts are included in
the assumed potential-node tree and do not execute packet ring methods
during their structural scans.

The conditional whole-frame reference now exposes
`paper_packet_outer_ring_call_envelope` when the literal paper schedule
actually contains active levels. Both the descriptor count and the mode
state bound are conditional on successful packing and shrinkage. The
source's original and inherited Sudoku oracles have separate accounting.

## Unresolved

The ceiling may itself be enormous. In particular,
`(K+1)^L` captures a source-level table-growth obstruction. A finite
operation count does not establish subexponential *bit* complexity.

Remaining proof obligations include: a uniform bit-work bound for each
ring operation at all inherited precisions and nested coefficient
representations; non-ring integer powers and key allocations;
generated packet preparation; **actual retained working-set memory**;
numeric fallback without capacity refusals; and the conversion from
network-edge scale to Sudoku cell count. Native/lazy implementations
require separate source correspondence and cost models.

The deliberately red worst-case theorem test remains red.
