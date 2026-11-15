# Optimistic packet-packing gap under replacement leaf cutoffs

**15 November 2026.** This is a finite-size **no-go for a specific uniform *sufficient-condition proof strategy***, not a complexity lower bound for tensor contraction and not a new executable ETH algorithm.

Source: OpenAI's [quantitative-contraction.tex](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex), pinned observed Git blob `51ba54efc29f51bbc0426f848003030da484f354`, “Parameters and collision packing” and “The child networks and their descriptions”. Replacement finite graph lemma: [matching-potential packing](matching-potential-packing.md). The original leaf cutoff obstruction is analyzed separately in [two-adic depth gate](two-adic-depth-gate.md).

## Why simply lowering H does not close the algorithm

The paper fixes a direct leaf at
\[
H=\left\lceil s/\lfloor\sqrt\lambda\rfloor\right\rceil,
\]
far larger than any practical direct summation at finite sizes. A proposed replacement might use a much smaller leaf edge budget \(B\), for example \(B=20\), so a direct leaf enumerates at most \(2^{20}\) Boolean edge assignments, *before* entry-evaluation overhead.

But decreasing the cutoff forces recursion to continue deeper. The packet-label alphabet grows with every positive-width active step. The source's per-depth formulas require
\[
a_d=2\sum_{j=0}^d u_j,\quad
L_d=2^{a_d},\quad D_d=r^{2a_d}.
\]
Every nonzero integer width satisfies \(u_j\ge1\), so
\[
a_d\ge2(d+1),\quad L_d\ge4^{d+1},\quad
D_d\ge r^{4(d+1)}.
\]

The improved matching-potential *sufficient* packing lemma also requires a maximum degree cap \(\delta_d\ge2L_d\). To give a hypothetical schedule the **best possible numerical chance**, pretend its actual degree cap can be minimized independently at every level:
\[
\delta_d=2L_d.
\]
This is optimistic, not a proved all-depth invariant; in reality old vertex degrees can persist and force a larger cap.

The resulting **smallest possible sufficient threshold** at depth \(d\) is

\[
\boxed{
T_d=r^{4(d+1)}
\left[
(4\cdot4^{d+1}-1)
\left\lceil\log_2\bigl(r^{4(d+1)}\bigr)\right\rceil
+4^{d+1}
\right].
}
\]

It is a mathematical lower bound on the edge count required by the *new sufficient theorem* at that depth, assuming \(u_j\ge1\) for every previous active level. It is **not** a lower bound on the actual number of edges needed for a successful instance-specific packet layout. The implementation can check and refuse on arbitrary-precision thresholds exceeding `u128` without constructing any network.

Independently, if ancestors actually satisfy that packet lemma, the source gives
\[
M_{d+1}\le\frac6r M_d.
\]
Define the *optimistic upper envelope* \(U_0=s\),
\(U_{d+1}=\lfloor6U_d/r\rfloor\), for \(r\ge7\).
Any real child is at most \(U_d\). The proposed direct-leaf budget \(B\) is **guaranteed** once \(U_d\le B\), conditional on successful packing at every preceding active call.

Thus a depth with
\[
\boxed{B<U_d<T_d}
\]
is an **uncovered active-size range**: if a child of size between \(B+1\) and \(U_d\) occurs, it is neither a proposed direct leaf nor admissible under the replacement packing theorem's sufficient inequality. It might still be packable in reality, and actual children might be smaller than \(B\). The statement is an obstruction to a uniform proof that relies **only** on these two inequalities and the proposed leaf cutoff.

## Exact examples

For \(s=10^{10}\) tensor-network edges and a proposed direct-leaf budget \(B=64\):

| Groups \(r\) | Earliest uncovered depth | Prefix passing *optimistic* packing arithmetic | Depth at which \(U_d\le64\) |
|---|---:|---:|---:|
| 7 | 2 | 2 levels | 123 |
| 8 | 1 | 1 level | 66 |
| 16 | 1 | 1 level | 20 |
| 49 | 1 | 1 level | 9 |
| 64 | 1 | 1 level | 8 |

At \(r=64\), the root threshold is \(T_0=6{,}106{,}906{,}624\). The first child has at most \(937{,}500{,}000\) edges, but even the *optimistic* depth-one threshold is
\(T_1=855{,}683{,}929{,}200{,}394{,}240\). This is an uncovered interval, not merely a disappointing performance constant.

At \(r=7\), the root threshold is \(T_0=441{,}784\) and the second stage needs \(T_1=8{,}445{,}433{,}465\), which is below its maximum child-size bound \(U_1=8{,}571{,}428{,}571\). But at depth two, \(T_2=120{,}889{,}802{,}413{,}534\) greatly exceeds \(U_2=7{,}346{,}938{,}775\). A smaller \(r\) helps packet-label capacity but slows the proven reduction in child size.

For a **more plausible direct-summation exponent** \(B=20\), the corresponding guaranteed leaf depths become 130 for \(r=7\) and 9 for \(r=64\), while the uncovered packing depths remain 2 and 1. The number \(2^{20}\) accounts for assignments only, not coefficient/field cost.

Even at the artificial maximum \(s=2^{128}-1\) with \(B=128\), the first uncovered depths are 8 (\(r=7\)) and 4 (\(r=64\)), whereas \(U_d\le128\) is guaranteed only at depths 544 and 36. This is a mathematical *finite-width* audit, not an asymptotic impossibility theorem.

## Reproducibility and refusal semantics

```sh
cargo test --locked -p lean-eth-reference --test appendix_basecase_gap
cargo run --locked -p lean-eth-reference --bin appendix-basecase-gap -- 10000000000 64 20
cargo run --locked -p lean-eth-reference --bin appendix-basecase-gap -- 10000000000 7 20
cargo run --locked -p lean-eth-reference --bin appendix-basecase-gap -- 340282366920938463463374607431768211455 64 128
```

Every CLI invocation intentionally exits with status 2 and `sat_count=null`; it reports the first uncovered active depth, the optimistic matching threshold, the conditional child-size upper bound, and the depth required to guarantee the proposed leaf budget. The fields `source_recursion_admitted=false` and `tensor_contraction_executed=false` are not overridden by arithmetic success. All relevant integers use checked `u128` operations and string-encoded receipt values. The public proof works over unbounded integers; the prototype explicitly refuses unrepresentable thresholds.

## Research decision

Changing only the **root packet width**, only the **collision concentration estimate**, or only the **leaf cutoff** will not give a complete finite-size proof using the remaining source invariants. To close the uncovered ranges, at least one substantive new lemma is needed:

1. **Depth-stable / resetting label scheme.** Avoid cumulative \(a_d=2\sum_j u_j\), or prove a new packet construction with substantially smaller effective \(D_d\). This would require re-proving the integral deformation, mode routing and interpolation semantics. We cannot simply reset the source coordinates.
2. **Instance-certified structural base cases.** Instead of direct summation, exploit a precisely certified graph property such as small treewidth, disconnected components, or affine constraints. Such a base case may improve real instances but is **not** a worst-case guarantee unless the structural property is proved for every unsupported child.
3. **Uniform packing below the new sufficient threshold.** Improve the sufficient packing theorem or characterize packet layouts directly, with proof that every child in \((B,U_d]\) can be handled without exceeding the original full-cost budget.

Any alternative must include the actual source-defined packet coefficients and signed mode contractions, proof of precision and canonical lifting, and measured field/setup/branch/leaf/bit work. Replacing a large direct leaf with an unverified exact solver or exhaustive enumeration is not an ETH algorithm improvement.

[Main acceptance issue #258](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/258)
