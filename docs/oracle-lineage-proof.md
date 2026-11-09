# Oracle lineage across recursive packet children

**Status: a proved structural reference-identity invariant and a conditional
single-path descriptor-count bound, not a complete bit-cost theorem.**

The new source-correspondence checker is `reference/oracle_lineage.py`.
The actual `make_child` and `CompiledChildPlan.instantiate` implementations
construct every retained parent vertex as a new `Vertex` containing the
**identical** `vertex.oracle` callable. Neither turns that original callable
into a lambda wrapper or performs a copy of its closure. Each selected
nonempty packet instead creates one `PacketEntry` that evaluates its own
prepared ring coefficients, mode terms and edge-assignment bits. The packet
constructor does not put a direct reference to the parent Network or parent
callbacks into its own fields.

This is a useful description-size property: the inherited callback is a
*shared reference*, not an expression whose syntax incorporates its parent
descriptor recursively at every layer.

## One child, with actual source correspondence

Write `M_d` and `V_d` for the parent network's edge and vertex counts,
and `P_d` for its packed nonempty packet count. `pack` partitions every
parent edge exactly once into packets and omits empty packets. Thus

\[
0\le P_d\le M_d.
\]

At a given group and coordinate, each parent vertex is either omitted or
retained exactly once. Each selected packet produces at most one new right
vertex whose oracle is a `PacketEntry`. Hence

\[
V_{d+1} \le V_d + P_d \le V_d + M_d.
\]

The checker validates these properties on concrete child networks, including
component-restricted and compiled-plan paths, and rejects forged inherited
callbacks, forged packet callbacks, and invalid packet ownership.

## A complete successful *single path* of literal paper recursion

The actual live paper child check requires

\[
32 M_{d+1}\le 3 M_d
\]

at every active recursive edge. Therefore, for a root with `M_0` edges
and `V_0` vertices,

\[
\begin{aligned}
V_d
&\le V_0+\sum_{j<d}P_j\\
&\le V_0+\sum_{j\ge0}M_0(3/32)^j\\
&=V_0+\frac{32}{29}M_0.
\end{aligned}
\]

Since the descriptor count is integral, the checker returns the explicit
bound `V_0 + floor(32*M_0/29)`. This bounds the number of visible oracle
*references/descriptors on one descendant network* and the total number of
new packet descriptors instantiated **along one selected chain**.

The path bound does NOT bound the total number of generated children in the
recursion tree. Nor does it bound caches retaining packet descriptors from
many siblings, memory ownership, coefficient bit lengths, per-packet
preparation, or the work of calling any inherited or original oracle.

## What this closes, and what it does not

The **vertex-count term** in a whole-frame size recurrence is now justified
by explicit source identity, including second-generation packet retention.
A generated packet entry uses finite local coefficient data instead of
recursively embedding the parent callback's program text.

However, an original input vertex is an arbitrary Python callback. It may
take arbitrarily many instructions or fail to return. The identity bound
alone cannot assign any bit cost to that callback. Existing packet evaluation
and preparation envelopes cover only declared eager Python coefficient paths;
they still do not cover native inner loops, lazy expression graphs, dynamic
allocator costs or all terminal fallbacks.

Do not remove
`input_oracle_bit_contract_and_uniform_metadata` from the unresolved
whole-frame theorem premises or mark the intentionally red research
acceptance test green. The remaining task is to combine a *restricted,
uniformly bounded original Sudoku-oracle ABI* with the existing
packet-evaluation and local-preparation bit-cost lemmas, and then establish
total non-refusing execution and the correct Sudoku cell-size parameter.

Run the invariant suite:

```bash
PYTHONPATH=src:. python -m pytest -q tests/unit/test_oracle_lineage.py
```
