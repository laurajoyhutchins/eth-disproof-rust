# Orbit-sparse packet layout

**15 November 2026. Status:** implemented finite, bounded Rust layout with independent structural regression checks. **Not** a proved replacement for the appendix's tensor recursion. The source is OpenAI's [quantitative-contraction.tex](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex), observed Git blob `51ba54efc29f51bbc0426f848003030da484f354`, especially the packing lemma and Cauchy deformation.

The [previous depth audit](two-adic-basecase-gap.md) showed an independent obstacle: padding every ordered label-pair class to a common `H_pad` makes the packet count grow with all `D=r^(2a)` classes even when most classes contain no edges. This document changes the *finite packet layout*, not the root width schedule, the original mathematical claims, or the counting algorithm.

## Deterministic orbit-sparse construction

For a fixed, explicitly labelled bipartite multigraph, group source edges by the **unordered coordinate-pair signature** `sigma=((min(row_i,col_i),max(row_i,col_i)))_(i<a)`.

For an occupied signature `sigma`, put:

- `e_sigma`: number of coordinates with equal symbols;
- `c_sigma=2^(a-e_sigma)`: number of ordered label-pair classes in its orientation orbit;
- `q_sigma=2^e_sigma=L/c_sigma`: number of slots *per ordered class per packet*;
- `X_gamma`: number of real source edges in ordered class `gamma`;
- `x_sigma=max_gamma X_gamma`, including orientations with zero real edges.

Allocate exactly

\[
\boxed{P_\sigma=\left\lceil\frac{x_\sigma}{q_\sigma}\right\rceil}
\]

packets for this occupied orbit, and **no packets** for unoccupied signatures. Within each packet, every slot index `0..L-1` has precisely the appendix's semantics: at an unequal coordinate, the slot bit chooses the ordered symbol orientation; at an equal coordinate, that bit chooses the copy index. The `j`th packet takes edge index `j*q_sigma+copy_index` from the selected ordered class, if present, otherwise a genuinely unused slot with no port. This preserves each real source edge's identity and common slot at both ends.

A `BTreeMap` orders signatures and class/edge assignments reproducibly. The bounded Rust reference uses `a<=3`, `2<=r<=64`, `M<=256`, checked capacities and a cap on materialized packet slots. It never enumerates all `D` ordered classes.

This construction may change which *real* ports share a packet relative to the original uniform construction. The source Cauchy deformation then differs at \(T\ne0\). The original count at \(T=0\) remains the relevant target, but a formal proof that the source's mode/interpolation/group identities apply to this **new layout** is still required.

## Source Cauchy interpolation at the original point

The appendix defines, for row/column positions `x,y` in one packet,

\[
W_{xy}(T)=\frac{\mathcal C(T)}
{\mathcal C'(0)(T-(y-x))},\qquad
\mathcal C(T)=\prod_{t=-L}^{L-1}(T-t),
\]

with cancellation of the factor \(T-(y-x)\) before evaluating.
Between distinct packets it sets \(W_{xy}(T)=0\), and it restricts
the matrix to **real ports**. Since \(y-x\) is one of the roots of
\(\mathcal C\), the exact polynomial identity gives
\(W_{xy}(0)=1\) when the two real ports occupy the **same**
slot and zero otherwise. For each occupied source edge the sparse
constructor places its row and column port at the same position;
all real source edges are unique. Thus **\(W(0)=I_M\)** for this
finite layout without reference to empty signatures or to the
original all-class padding.

Consequently, if \(A(Y)\) and \(B(X)\) denote arbitrary source
row/column tensor products over Boolean edge assignments, the
appendix's displayed deformation satisfies

\[
\begin{aligned}
F(0)
 &=\sum_{X,Y}A(Y)B(X)
   \prod_x\ell_{Y_x}((W(0)X)_x)\\
 &=\sum_X A(X)B(X),
\end{aligned}
\]

since \(\ell_0(z)=1-z\), \(\ell_1(z)=z\), and
\(\ell_{Y_x}(X_x)\) is the equality indicator for Boolean values.
This is an **algebraic original-point identity for any port-faithful
layout**, including orbit-sparse, and does *not* require
factorization of internally coupled tensor factors.

An independent Rust regression evaluates the cancelled Cauchy
polynomial at \(T=0\) in exact \(i128\) arithmetic for the
two-coordinate finite witness. It checks the full real-port
\(W(0)\) matrix and exhaustively verifies the last equality with
coupled, signed row and column tensor functions. This is important
progress on the source-semantic boundary, but **does not transfer
the \(T\ne0\) precision, weighted-mode or group-routing theorems**.
Changing which real ports share a packet changes \(W(T)\) away
from zero and must be re-proved at that level.

## Exact waste identity and structural admissibility

For each occupied orbit write `M_sigma=sum_gamma X_gamma`. Its padded slots are `P_sigma*L`, and its two sources of waste are:

\[
E_\sigma=c_\sigma x_\sigma-M_\sigma\ge0
\quad\text{(unequal orientation loads)},\qquad
R_\sigma=LP_\sigma-c_\sigma x_\sigma\ge0
\quad\text{(copy-index rounding)}.
\]

Summing over occupied orbits,

\[
\boxed{PL=M+E+R,\qquad
E=\sum_\sigma E_\sigma,\quad
R=\sum_\sigma R_\sigma.}
\]

This proves an **exact, testable** packet-count characterization for a fixed labeling:

\[
\boxed{P\le 3M/L\iff E+R\le2M.}
\]

The statement is independent of the global label-space size \(D\). It is not a worst-case existence theorem for balanced labels. An immediately checkable sufficient budget is \(E+K(L-1)\le2M\), where \(K\) is the number of occupied orbits, because \(0\le R_\sigma<L\). The reference records exact `E`, `R`, and \(P\).

A packet-count certificate alone is **not** the full packet lemma. The original bound also requires every coordinate symbol to have at most \(3M/r\) *actual* row ports and at most \(3M/r\) actual column ports. These real-port counts are unchanged by omission of empty packets, but they can be badly unbalanced for a particular labeling. The reference computes and verifies the exact counts and therefore the derived maximum of \(6M/r\) child edge incidences. Original graph degrees and the new-packet bound \(2L\) are independently checked against the supplied degree cap.

Only `construct_orbit_sparse_admitted` returns a **structurally admitted layout** when all the appendix's packet, symbol-port and degree bounds hold. `construct_orbit_sparse_bounded` returns a labelled graph's concrete layout with explicit failure booleans, useful for inspecting counterexamples. Neither function admits the original tensor recursion.

## Small witnesses and counterexamples

| Finite graph and labels | Real edges | Sparse packets | Uniform construction | Packet/port result |
|---|---:|---:|---|---|
| `r=2,a=2`, 16 independent edges, every row/column label zero | 16 | 4 | Refuses all-class load bound | Both pass |
| `r=2,a=1`, two edges in each ordered class | 8 | 4 | 4 packets | Same exact layout |
| `r=2,a=2`, four edges in one all-unequal orientation | 4 | 4 | Refuses | **Packet count fails**, port balance passes |
| `r=4,a=2`, 16 edges in one equal-symbol class | 16 | 4 | Refuses | Packet count passes, **symbol ports fail** |
| `r=64,a=2`, 256 independent edges across 64 diagonal symbol signatures, four per signature | 256 | 64 | Global class enumeration exceeds bounded reference | **All structural bounds pass** |

The last fixture is especially instructive. It has `L=4` and `D=64^4=16,777,216` potential ordered classes, but only 64 occupied orbits. Each group-symbol child has exactly eight real edge incidences, and all 256 input edges are retained with zero padded slots. This is a **finite structural certificate**, not an end-to-end count. The published root width remains zero for `M=256`, and the source's large-input asymptotic width, precision and depth conditions are not verified by it.

The two concentrated counterexamples show why one cannot replace the original lemma with the statement “sparse padding always works.” At `a=2`, an all-unequal orbit has `q=1`. If all edges use one orientation, each edge occupies one four-slot packet, so \(P=M>3M/4\), even if the per-symbol port bound happens to hold. In an all-equal orbit, \(q=L\) minimizes padding, but one symbol can receive too many ports.

## Verification and cost boundary

```sh
cargo test --locked -p lean-eth-reference --test orbit_sparse_packet_layout
cargo test --locked -p lean-eth-reference --test appendix_orbit_sparse
cargo run --locked -p lean-eth-reference --bin appendix-orbit-sparse -- r64-balanced
cargo run --locked -p lean-eth-reference --bin appendix-orbit-sparse -- r2-concentrated-unequal
```

The CLI intentionally returns status code **2** and `sat_count=null`. Its JSON includes orbit-level `E/R` waste, real/padded edge counts, actual port and child incidences, and independent structural admission booleans. It explicitly states `source_sparse_tensor_semantics_proved=false`, `source_precision_and_routing_proved=false` and `recursion_executed=false`.

Tests independently enumerate all 15 nonempty simple 2-by-2 bipartite edge subsets and all \(4^4=256\) assignments of `r=2,a=2` labels per graph. They reconstruct orbit counts and packet slots independently from the constructor, verify source edge identity, slot orientation, copy bits, exact waste identity and separate packet/port conditions. They also cover parallel edges, real absent slots, invalid labels, degree refusals and the original uniform-layout comparison.

Materializing the packets takes \(O(Ma+PLa)\) operations up to balanced-tree map overhead, since unoccupied signatures are never enumerated. But this **excludes the cost of finding a labeling that passes both bounds**, exact packet tensor entry generation, coefficient arithmetic, field setup, interpolation, weighted-mode enumeration, recursion and leaves. Those must enter any end-to-end cost receipt. The current bounded reference is not a proof of a useful worst-case time bound.

## Degree-weighted simultaneous port balancing

A [deterministic joint labeler](two-adic-joint-orbit-balance.md)
now provides an independent, universal **per-symbol port theorem**:
\(rC\le M+(r-1)\Delta\). Consequently
\((r-1)\Delta\le2M\) suffices for both shore port bounds
in every coordinate. A necessary obstruction for **any** vertex
labeling is \(r\Delta\le3M\). Both apply to multigraphs.

The labeler then tries only polynomially many coordinatewise cyclic
relabelings of the right shore. Every trial preserves the port
loads but can reduce the exact orbit waste \(E+R\). For a
32-edge, \(r=4,a=2\) shifted matching, this reduces 32
sparse packets to eight without changing port counts.
**No universal orbit-waste bound is proved**; structural admission
still checks the exact packet and child bounds and refuses failures.

## Mathematical next steps

1. Formalize `OrbitSparsePacketLayout` and the exact `PL=M+E+R` count, assignment bijection, slot-orientation and port-count invariants in Lean. Admit only verified degree/packet/port receipts.
2. Prove whether **removing entirely empty packets** is transparent to the source Cauchy deformation after restriction to real ports, and whether independently shrinking occupied orbit capacities changes only the interpolation instance rather than the recovered \(F(0)\).
3. Prove the full source packet-entry and weighted-mode routing identities for the changed layout. A structural packet witness is insufficient to discharge source `hpacket`/`hroute` in the full recursion.
4. Develop a deterministic, globally balanced vertex-labeling method that simultaneously bounds orbit imbalance `E`, rounding `R` and per-symbol real ports on arbitrary bounded-degree child networks; or identify a concrete worst-case counterexample. The previous matching-potential method controls **ordered class loads**, but not this orbit-specific objective.
5. Re-run the all-depth audit with a **proved** new per-level packet/degree/precision bound, and only then execute one exact nonterminal contraction with full cost and an independent count baseline.

See [orbit-sparse implementation issue #291](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/291) and [complete recursion acceptance #258](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/258).
