# Multi-level depth gate for the two-adic tensor contraction

**15 November 2026.** Exact child-size and leaf-threshold arithmetic, using OpenAI's [quantitative-contraction.tex](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex), source Git blob `51ba54efc29f51bbc0426f848003030da484f354`. This is **not** a complete recursive algorithm, field computation, precision theorem or count.

The newly merged [matching-potential packet lemma](matching-potential-packing.md) improves the original root collision-loading condition. That alone does not make deeper recursion practical. The source uses two **independent** restrictions:

\[
H=\left\lceil\frac{s}{\lfloor\sqrt\lambda\rfloor}\right\rceil,
\quad \lambda=\lceil\log_2s\rceil,
\qquad
M_{d+1}\le\frac{6}{r}M_d.
\]

A call with `M<=H` is a **direct-summation leaf**. The child-size inequality is derived from the packet lemma's `3M/r` row and column port bound. It is conditional on successful packing and does not, by itself, guarantee any child with nonzero edges.

## Source r=64: a universal two-active-level ceiling within u128

For the original `r=64`, let `M_0=s`. Any produced first-generation child has `M_1<=3s/32`, and every second-generation child has

\[
M_2\le \frac9{1024}s.
\]

For `2<=s<=2^128-1`, `lambda<=128`, thus `floor(sqrt(lambda))<=11` and `H>=s/11`. Because `9/1024<1/11`, **every second-generation child is necessarily a leaf**. No third active call is possible, irrespective of collision-label construction or positive `u` schedule. This extends to any `r>=49` that retains the source's strict `M/8` shrink guarantee, because `(6/49)^2<1/11`.

For `lambda<=120`, `floor(sqrt(lambda))<=10`, so `H>=s/10`. But `M_1<=3s/32<s/10`. **Every first-generation child is a leaf**. A second active level is numerically *possible* only for `lambda>=121` (root sizes strictly larger than `2^120`), and might still be absent depending on actual packet structure.

These are depth bounds for this source choice of `H` and child-size guarantee. They are **not** lower bounds on all #SAT or tensor algorithms. An alternate leaf cutoff would require an independent cost/precision proof and could change the argument.

## The published degree envelope still defeats improved packing

The matching-potential sufficient condition is strictly better than the
original quadratic collision requirement, but substituting the original
maximum-degree envelope \(\Delta=\lceil s^{9/10}\rceil\) still fails
for every positive \(u\), \(r\ge7\) and \(2\le s\le2^{128}-1\).

Indeed, \(s^{1/10}<2^{13}\) gives \(\Delta\ge s/8192\).
At positive root width, \(a\ge2\) and
\(D=r^{2a}\ge7^4=2401\), hence
\(\lceil\log_2 D\rceil\ge12\). Since
\(2\Delta-1\ge\Delta\) for \(\Delta\ge1\), the
matching-potential sufficient condition would imply

\[
s\ge D(2\Delta-1)\lceil\log_2D\rceil
\ge\frac{2401\cdot12}{8192}s>s,
\]

a contradiction. This is an obstruction to **using that worst-case
degree bound to establish the sufficient condition**, not proof that
actual graphs cannot be packed. A tighter degree invariant proved
for the original network and all of its children is indispensable.

The `appendix-packing` refusal receipt now reports this new
obstruction separately from the *old lemma's* obstruction.

## The source schedule is still completely inactive

The original `u_d=floor(lambda/(131072*2^d))` gives `u_0=0` for every such `s`. Our analysis permits **hypothetical nonzero widths** only to isolate what happens if that independent obstruction is removed. It must not be reported as a faithful execution of the original schedule.

For candidate widths `u_0,u_1,...`, the exact source parameter formulas are

\[
a_d=2\sum_{j=0}^d u_j,\quad L_d=2^{a_d},\quad D_d=r^{2a_d}.
\]

The new packing sufficient bound for a proposed **uniform** maximum degree `delta` is

\[
M_d \ge D_d((2\delta-1)\lceil\log_2D_d\rceil+L_d),\quad
\delta\ge2L_d.
\]

Our audit compares this threshold to the **largest possible child edge count**, iterating `floor(6M/r)` exactly. If the upper bound is smaller than the threshold, this *sufficient method* cannot certify the node, but an actual packet layout could still be feasible without the sufficient inequality. Conversely, if the upper bound exceeds the threshold, this does **not** prove the real child has enough edges, that a degree invariant survives, or that recursion is correct.

## Concrete results

| Hypothesis | Consequence |
|---|---|
| `s=6,106,906,624, r=64, delta=8, u=[1,1,1]` | Root meets new *packing arithmetic*, but first child is guaranteed a direct leaf; \(H=1{,}221{,}381{,}325\) |
| `s=2^120, r=64, delta=32, u=[1,1,1]` | \(\lambda=120\); first child guaranteed leaf |
| `s=2^120+1, r=64, delta=32, u=[1,1,1]` | \(\lambda=121\); first child could be active, second generation guaranteed leaf |
| `s=2^128-1, r=64, delta=32, u=[1,1,1]` | Both root and first child can meet the *numerical* packing threshold, but third call cannot be active; \(H=30{,}934{,}760{,}629{,}176{,}223{,}951{,}215{,}873{,}402{,}888{,}019{,}224\) |

The last row represents an astronomical tensor graph, not a practical benchmark. Its degree cap is only a **hypothetical assumption**. The original schedule and precision/recovery conditions still fail to transfer.

### Reproducible receipts

```sh
cargo test --locked -p lean-eth-reference --test appendix_depth
cargo run --locked -p lean-eth-reference --bin appendix-depth -- 6106906624 64 8 1,1,1
cargo run --locked -p lean-eth-reference --bin appendix-depth -- 340282366920938463463374607431768211455 64 32 1,1,1
```

Both CLI calls intentionally return exit code 2 and print exact JSON with root \(\lambda\), nominal leaf exponent \(H\), cumulative \(a_d\), proposed widths, candidate degree cap, conditional per-depth upper edge counts, matching-potential arithmetic and reason for refusal/leaf. All large integers are decimal strings; no approximate floating-point decisions are made.

The receipt always has `full_recursion_admitted=false`, `degree_invariant_verified=false`, `precision_schedule_verified=false`, `tensor_contraction_executed=false`, and `sat_count=null`. Arithmetic success is never treated as an execution.

## Implications for the actual algorithm

1. The new matching potential is a mathematically useful change of the packet **sufficient condition** and is independently testable in bounded Rust graphs.
2. With the original \(H\) and \(r=64\), it cannot produce more than a shallow recursion on any `u128` graph. The surviving direct leaf remains far too large for direct summation.
3. A practical contraction must change the **leaf/base-case strategy or the shrinkage/precision schedule**, with a new proof of the total bit complexity. Reducing only collision packing or `epsilon` cannot establish an executable ETH disproof.

This is not a claim that a better schedule cannot exist. It identifies an additional independent acceptance gate for [issue #258](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/258).
