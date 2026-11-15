# Simultaneous symbol-port and orbit-packet balancing

**15 November 2026.** A bounded, deterministic, source-slot-connected labeling construction. This establishes a universal **per-coordinate port-balancing theorem** and an **instance-certified** orbit-packet search. It does not establish a universal orbit-waste bound or a valid full counting recursion.

See [the original source packet lemma](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex), [orbit-sparse packet construction](two-adic-orbit-sparse-layout.md), and [complete source recursion acceptance](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/258).

## The independent port theorem

Consider any bipartite multigraph, with \(M\) real edges, maximum vertex degree \(\Delta\), \(r\ge2\) coordinate symbols and \(a\ge1\) coordinates. On each shore and in each coordinate, treat each vertex as one indivisible item of weight equal to its degree. The total weight on either shore is \(M\).

Assign vertices one at a time to a currently least-loaded of the \(r\) symbol bins. Degree-descending order is deterministic; a coordinate-dependent cyclic tie preference is deterministic too. For **any** processing order, every final symbol load \(C\) satisfies

\[
\boxed{rC\le M+(r-1)\Delta.}
\]

Proof: consider the final item, of weight \(w\le\Delta\), assigned to the bin which eventually has load \(C\). Before that item was assigned, the bin was minimum loaded, so its load was at most the total assigned weight divided by \(r\), which is at most \((M-w)/r\). Thus \(C\le(M-w)/r+w\le(M+(r-1)\Delta)/r\). Subsequent loads to other bins cannot increase this bin. This proof applies independently to both shores and all coordinates. It does **not** assume independence of edge endpoints or bounded collision concentration.

The source's real-port requirement is \(C\le3M/r\), so the explicit sufficient condition

\[
\boxed{(r-1)\Delta\le2M}
\]

guarantees every row-symbol and column-symbol port cap, hence each coordinate-symbol child has at most \(6M/r\) real edge incidences. This removes one **independent finite source-packet structural obligation** when that degree condition holds. Existing source packet vertices still require a separately verified maximum-degree invariant \(2L\le\Delta_{\rm cap}\), and the full precision/recovery theorem does not follow.

There is also a simple, genuinely **necessary** port obstruction for any vertex labeling:

\[
\boxed{r\Delta\le3M.}
\]

A maximum-degree vertex chooses a single symbol in each coordinate and contributes all \(\Delta\) incidences to that symbol on its shore. If \(r\Delta>3M\), no possible vertex labels can satisfy the source port bound. The reference returns a refusal **before** running a packet search. The gap between this necessary condition and the greedy sufficient condition is not resolved by this theorem.

These bounds apply to each actual child graph if its \(M_d\) and \(\Delta_d\) satisfy the hypotheses. They do not automatically prove \(\Delta_d\) is preserved along the source's recursive tensor transformation.

## Orbit-aware local improvement with the port invariant preserved

The port labels from weighted bin assignment need not have small orbit waste. Following the [sparse packet identity](two-adic-orbit-sparse-layout.md), the precise objective for any labelled graph is

\[
PL=M+E+R,
\]

with orientation imbalance \(E\) and copy-slot rounding \(R\). The desired source packet-count condition is \(E+R\le2M\).

Crucially, adding a fixed \(k\bmod r\) to **every right-shore label in one coordinate** permutes the right-shore symbol names. It preserves the entire **multiset of port loads** on that shore, leaves all left-shore counts unchanged, and never changes original vertex degrees. It can, however, change which row/column symbol pairs are equal, which swap-orbits are occupied, and the value of \(E+R\).

The bounded implementation performs deterministic coordinate descent over these cyclic permutations, enumerating at most \(1+a(r-1)q\) complete packet-layout evaluations for \(q\le3\) sweeps. It accepts a change only if the **exact** number of padded packets decreases strictly. It therefore never worsens the packet count or any source per-symbol port maximum. It is polynomial-time in the graph representation for the bounded parameters; it does not enumerate exponentially many global labelings.

**Important limitation:** a local optimum is not a universal guarantee that \(E+R\le2M\). The implementation separates these truths:

* `construct_joint_balanced_bounded` returns a deterministic best-found layout, with exact, separately checked packet and port bounds, even if packet structural admission fails.
* `construct_joint_balanced_admitted` refuses whenever the resulting packet count, per-symbol port counts, or child edge incidences exceed the source packet-lemma structural caps.
* Both functions remain **unsupported** as source-defined nonzero tensor deformations or full counting algorithms.

## Exact finite examples

| Graph | Initial sparse packets | Optimized sparse packets | All-class uniform packets for the final labels | Source structural bounds |
|---|---:|---:|---:|---|
| \(r=4,a=2,M=32\), shifted independent matching | 32 | 8 | 512 | Certified |
| \(r=64,a=2,M=256\), independent diagonal matching | 64 | 64 | 16,777,216 | Certified |
| \(r=4,a=2,M=16\), degree-16 star | Refused before search | Refused | Not applicable | Provably impossible: \(r\Delta=64>3M=48\) |

For the 32-edge matching, both shores have 32 degree-one vertices. The edge at left index \(i\) connects to the right index \(4\lfloor i/4\rfloor+((i+1)\bmod4)\). The independent degree-balanced initial labels differ by one symbol in both coordinates; initially there are four all-unequal occupied orbits, each using eight packets and leaving 96 empty slots. Two cyclic right-shore shifts of \(-1\bmod4\) align the symbols on both coordinates, giving eight fully occupied packets. The real symbol-port maximum on each shore stays at eight, well below the source's \(3M/r=24\) cap. The 512-packet uniform baseline is the original **mathematical** all-class layout count on those *same final labels*, not a timed execution of the old bounded implementation.

For the \(r=64\) matching, degree-weighted bin labeling already yields four edges per diagonal orbit and zero sparse padding; the full uniform construction would allocate one packet for each of the \(64^4\) ordered label-pair classes. Here again the source's fixed \(u_0=0\) for this finite graph, so this is **not** a source-active schedule.

For every fixed label assignment with at least one real edge, the sparse packet construction uses **no more packets than** uniform all-class padding: the global uniform padded load \(H_{\rm pad}\) is a multiple of \(L\), and for an occupied orbit with \(q\) copy slots per ordered class, its exact sparse packet count \(\lceil x/q\rceil\le H_{\rm pad}/q\). Summing over occupied orbits gives the comparison, with the unused orbits contributing only to the uniform count. The Rust receipt checks the actual finite inequality against an \(u128\) uniform packet-count calculation, **without materializing empty orbits**.

## Reproduction and cost

```sh
cargo test --locked -p lean-eth-reference --test joint_orbit_port_balance
cargo test --locked -p lean-eth-reference --test appendix_joint_balance
cargo run --locked -p lean-eth-reference --bin appendix-joint-balance -- r4-shifted
cargo run --locked -p lean-eth-reference --bin appendix-joint-balance -- r64-diagonal
cargo run --locked -p lean-eth-reference --bin appendix-joint-balance -- r4-star
```

The CLI returns status 2 for every invocation, reports `sat_count=null`, and includes exact initial/final packet counts, all-class comparison, symbol loads, checked search-evaluation count, degree/port proof flags and source-precision/refinement refusals. The star fixture exits without a success-looking JSON result. The search's finite test budget is explicit (at most three passes, 1,024 structural evaluations, 256 vertices per shore, 256 edges, \(a\le3\), \(r\le64\)).

The full computational cost includes the independent \(O(aVr)\) weighted bin scan and at most \(O(arq)\) *complete sparse layout evaluations* with exact edge and padding verification. Those are bounded, not optimized away. Nothing in this work establishes a polynomial-cost **complete** source tensor contraction; original field setup, packet-entry generation, interpolation, mode counts, recursion tree and direct leaves remain unmeasured and unverified here.

## What remains

1. Prove an all-graphs **joint orbit-waste and port** existence bound, or produce a rigorous obstruction under the source degree/size hypotheses. The bounded search gives finite witnesses, not a universal labeling theorem.
2. Formalize the greedy port theorem and source port identities in Lean, and prove that the changed sparse packet tensor deformation preserves nonzero Cauchy coefficients, weighted mode routing and tapered precision.
3. Prove the exact degree/precision constraints across every child, and a viable direct-leaf or source-faithful recursive schedule. The fixed source \(u_0\) and finite \(u128\) depth audit remain separate blockers.
4. Measure the complete source contraction against independent exact-count baselines. No speedup or ETH claim follows from the finite labeler.

See [issue #291](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/291).
