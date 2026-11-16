# A simultaneous structural labeling theorem

**15 November 2026.** This is a new **sufficient condition** for a
deterministically constructible vertex labeling whose *orbit-sparse*
packet layout meets both the source packet-count and symbol-port
requirements. The condition applies to **all bipartite multigraphs
with a certified maximum-degree bound**. It is not an ETH-disproof
acceptance result, not a new source schedule, and not a proof of
nonzero deformation or recursive tensor coefficients.

Starting points:
[the existing deterministic matching potential](matching-potential-packing.md),
[finite orbit-sparse slot construction](two-adic-orbit-sparse-layout.md),
[greedy symbol-port theorem](two-adic-joint-orbit-balance.md), and
[OpenAI's quantitative-contraction.tex](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex)
(observed source Git blob `51ba54efc29f51bbc0426f848003030da484f354`).

## Theorem

Let \(G\) be a finite nonempty bipartite **multigraph** with \(M\)
edges and actual maximum degree \(\delta\ge1\).
Fix integers \(r\ge2\) and \(a\ge1\), and define

\[
L=2^a,\qquad b=r^a,\qquad D=b^2=r^{2a},\qquad
O=\left(\frac{r(r+1)}2\right)^a,\qquad k=2\delta-1.
\]

Define integer logarithmic upper bounds

\[
t=\lceil\log_2(2D)\rceil,\qquad
h=\lceil\log_2(4ar)\rceil.
\]

Assume

\[
\boxed{
3M\ge 2\big(kDt+LO\big),\qquad M\ge4r\delta h.
}
\tag{1}
\]

Then there exists a **deterministically constructible vertex labeling**
by \(b\) equally likely labels on each shore such that:

1. Every ordered pair-label class \(\gamma\) has
   \(X_\gamma\le\frac{3M}{2D}+kt\).
2. Every actual symbol port load, on either shore and in every
   coordinate, obeys \(C_{\mathrm{shore},i,s}\le3M/r\).
3. In the finite orbit-sparse slot layout,
   \(P\le3M/L\), and the real incidence bound of every
   coordinate-symbol child is at most \(6M/r\).

If the graph is also subject to a **separately verified** packet
maximum-degree cap \(\delta_{\mathrm{cap}}\ge
\max(\delta,2L)\), the original graph vertices and new packet
vertices meet that *structural* degree cap.

This theorem **does not** establish source-defined packet tensor
values, correctness of the modified \(W(T)\) for \(T\ne0\),
group routing, 2-adic precision/canonical lifting, all-depth degree
induction, source admission, or any complete counting complexity.

### 1. A single normalized matching potential

Greedy edge coloring partitions the graph into at most
\(k=2\delta-1\) matchings; add empty matchings if necessary.
Independently assign each vertex a uniform label from \(b=r^a\)
possibilities. For an ordered class \(\gamma\) and matching \(j\)
of \(m_j\) edges, write \(X_{\gamma,j}\) for the number of
its edges assigned class \(\gamma\).

Matching edges have disjoint endpoints, so

\[
\mathbb E[2^{X_{\gamma,j}}]=(1+1/D)^{m_j}.
\]

Define \(A_{\gamma,j}
 =2^{X_{\gamma,j}}/(1+1/D)^{m_j}\).
The sum of conditional expectations over all \(kD\) terms
has initial expected value \(kD\).

### 2. A simultaneous normalized port potential

Let \(C_{\mathrm{side},i,s}\) count the sum of vertex degrees
on that shore whose \(i\)th coordinate digit is symbol \(s\).
Put

\[
z=1+\frac1{4\delta},\qquad
B_{\mathrm{side},i,s}
 =\frac{z^{C_{\mathrm{side},i,s}}}
 {\mathbb E[z^{C_{\mathrm{side},i,s}}]}.
\]

Each vertex contributes its entire degree \(d_v\) or zero
independently of the other vertices on that shore. Thus

\[
\mathbb E[z^{C_{\mathrm{side},i,s}}]
 =\prod_{v\text{ on shore}}
 \left(1+\frac{z^{d_v}-1}{r}\right).
\]

There are \(2ar\) normalized port terms, each with expectation
one. The combined potential is

\[
\Phi=\frac1{kD}\sum_{\gamma,j}A_{\gamma,j}
  +\frac1{2ar}\sum_{\mathrm{side},i,s}B_{\mathrm{side},i,s}.
\]

Its initial expectation is **exactly 2**. After any partial vertex
assignment, each of its \(b\) possible next labels has a
well-defined exact **rational** conditional expectation, and their
arithmetic mean is the current value. Choosing a minimum never
increases \(\Phi\). After labeling all vertices,

\[
\sum_{\gamma,j}A_{\gamma,j}\le2kD,\qquad
B_{\mathrm{side},i,s}\le4ar
\]

for *every* port. This establishes **one deterministic labeling**,
not the intersection of two unrelated existence results.

### 3. Ordered class bound

For one class \(\gamma\), AM-GM on its \(k\) nonnegative
matching terms gives

\[
\begin{aligned}
\prod_j A_{\gamma,j}
 &\le\left(\frac{\sum_j A_{\gamma,j}}k\right)^k
 \le(2D)^k,\\
2^{X_\gamma}
 &\le(2D)^k(1+1/D)^M.
\end{aligned}
\]

Using \(\log_2(1+x)\le x/\ln2\),
\(1/\ln2<3/2\) and
\(t\ge\log_2(2D)\) gives

\[
\boxed{X_\gamma\le\frac{3M}{2D}+kt}.
\tag{2}
\]

The normalization by \(kD\) is important: it does **not** insert
a spurious extra \(\log k\).

### 4. Every real port bound

For \(0\le d\le\delta\), convexity of \(x\mapsto z^x\)
and the binomial series imply

\[
z^d-1\le\frac d{\delta}(z^\delta-1)
 \le\frac d{3\delta},
\]

because \((1+1/(4\delta))^\delta<\sum_{j\ge0}4^{-j}=4/3\).
Consequently

\[
\mathbb E[z^C]
 \le\prod_v\left(1+\frac{d_v}{3r\delta}\right)
 \le\exp\!\left(\frac{M}{3r\delta}\right).
\]

From \(B\le4ar\), and
\(\ln z=\ln(1+1/(4\delta))\ge1/(4\delta+1)\),

\[
C\le(4\delta+1)
\left(\ln(4ar)+\frac{M}{3r\delta}\right).
\]

If \(M\ge4r\delta h\) with
\(h=\lceil\log_2(4ar)\rceil\ge\ln(4ar)\),
then \(\ln(4ar)\le M/(4r\delta)\), so

\[
C\le\frac{7(4\delta+1)}{12\delta}\frac Mr
 \le\frac{35}{12}\frac Mr
 <3M/r.
\]

The final port bound is strict before rounding; since \(C\)
is an integer, the source nonstrict cap follows.

### 5. Orbit-sparse packet count, including rounding

For each unordered coordinate-pair signature \(\sigma\),
let \(e_\sigma\) count equal coordinates.
An orbit contains \(c_\sigma=2^{a-e_\sigma}\)
ordered classes, with \(q_\sigma=2^{e_\sigma}
=L/c_\sigma\) slots per class and packet.
With \(x_\sigma=\max_{\gamma\in\sigma}X_\gamma\),
the orbit-sparse layout uses exactly

\[
P_\sigma=\left\lceil\frac{x_\sigma}{q_\sigma}\right\rceil
 \le\frac{x_\sigma}{q_\sigma}+1.
\]

For an empty orbit we count zero real packets; for an occupied
orbit the same upper bound holds. Summing even over all \(O\)
possible orbits,

\[
\sum_{\sigma}\frac1{q_\sigma}
 =\sum_{\sigma}\frac{c_\sigma}{L}
 =\frac DL
\]

because unordered orbits partition all \(D\) **ordered**
label-pair classes. By (2),

\[
\boxed{
PL\le \frac{3M}{2}+kDt+LO.
}
\]

The first inequality in (1) makes the RHS no greater than
\(3M\). The source packet-number, coordinate-symbol port and
child-incidence **structural** bounds therefore hold *together*.

### 6. Constructivity, complexity and exact arithmetic

To derandomize, choose vertices one by one. For each possible label,
evaluate the two normalized conditional-expectation sums **exactly**,
then select the smallest label giving the minimum sum.

For the matching potential, each unmatched edge contributes a
conditional numerator in \(\{D,D+1,D+b,2D\}\) over the same
denominator \(D+1\), depending on whether neither, one or both
endpoint labels have been set. The existing exact
matching-potential reference already uses that factorization.

For each port, define \(u=4\delta+1\), \(v=4\delta\).
A degree-\(d\) vertex contributes the integer numerator
\((r-1)v^d+u^d\) when unassigned,
\(ru^d\) when assigned to that symbol, and
\(rv^d\) otherwise, all with the same port expectation
normalizer. Multiplying the matching and port denominators
produces a **common positive integer** for comparisons.
No floating-point estimate is used in choosing labels.

Computing the potentials over \(b\) labels, \(D\) classes,
\(k\) matchings and \(2ar\) port terms requires polynomial
arithmetic work in the graph, \(b,D,k,a,r\) and the bit lengths
of the integer products. Under (1), \(D\le O(M)\) and
\(b\le\sqrt D\), so this is polynomial in the finite
edge-count representation, though it has large constants.
This is **not** the source's claimed total counting cost, which
includes tensor entries, weighted modes, child routing,
interpolation and leaf work.

The checked Rust `JointPotentialArithmetic` computes the sufficient
thresholds in `u128` without rounding a floating logarithm.
`None` from intermediate overflow means **unrepresentable**,
not a counterexample. A separate tiny
`construct_joint_potential_labels_small` reference uses checked
exact \(u128\) common-denominator rational numerators,
validates each vertex's full \(b\)-candidate averaging identity,
and checks final bounds and sparse slot layout. This
deliberately handles only \(M\le5\), \(r\le3\), \(a\le2\);
large-denominator overflow refuses instead of substituting
approximate arithmetic.

There is currently no large-input arbitrary-precision implementation
of the *combined* conditional potential. The theorem is constructive
mathematically, but the finite Rust witness does not execute at the
large sizes where (1) can actually hold.

## Exact threshold comparison

| \(r,a,\delta\) | Simultaneous packet threshold | Port threshold | Joint sufficient root M |
|---|---:|---:|---:|
| 64, 2, 8 | 4,205,841,067 | 18,432 | 4,205,841,067 |
| 7, 2, 8 | 314,221 | 1,344 | 314,221 |
| 64, 2, 32 | 17,627,613,867 | 73,728 | 17,627,613,867 |
| 2, 2, 1 | 78 | 32 | 78 |

These are **sufficient hypotheses** for all graphs with actual
maximum degree at most the specified \(\delta\), not
observed sample runtimes, practical-sized graphs or a completed
source root. The earlier matching-potential root threshold
for \(r=64,a=2,\delta=8\) was 6,106,906,624.
The new all-orbit rounding analysis reduces it to 4,205,841,067,
and simultaneously establishes a *port* bound.

The published global source envelope
\(\delta=\lceil s^{9/10}\rceil\) is still too coarse.
For every positive \(u128\) source root with positive width
\(a\ge2\) and \(r\ge7\), we have \(\delta\ge s/8192\),
\(D\ge2401\), \(t\ge13\), and \(k\ge\delta\).
The first sufficient inequality would require
\(s\ge(2/3)(2401)(13)\delta
 \ge (62426/24576)s>s\).
This says only that substituting the source **worst-case degree
envelope** cannot certify this improved sufficient theorem;
a smaller actual degree bound remains possible.

Furthermore, the original fixed \(u_0=0\) over the
\(u128\) edge-count range remains an independent
source-schedule obstruction. The exact depth and leaf cutoffs
are covered in [the all-depth audit](two-adic-depth-gate.md).

## Reproduction

```sh
cargo test --locked -p lean-eth-reference --test appendix_joint_potential
cargo test --locked -p lean-eth-reference --lib two_adic_joint_derandomize
cargo run --locked -p lean-eth-reference --bin appendix-joint-potential -- audit 4205841067 64 2 8 8
cargo run --locked -p lean-eth-reference --bin appendix-joint-potential -- tiny-mask 15
```

Every CLI returns **exit 2**. The arithmetic mode reports
`degree_bound_verified_from_graph=false`,
`actual_graph_labeled=false`, and `sat_count=null`.
Tiny finite exact witnesses show their chosen labels, rational
potential numerators, all conditional-average verification,
actual packet count and refusal flags. Neither mode executes
a source tensor contraction.

## Kernel-checked finite moments (15 November 2026)

The independent Lean formalization now contains two separate verified layers:

1. [`IndependentTwoAdicJointPotential.lean`](https://github.com/laurajoyhutchins/eth-disproof-rust/blob/main/rust/lean_eth_reference/proofs/IndependentTwoAdicJointPotential.lean), merged in [#306](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/306), proves the finite rational nonincreasing-choice principle, the concrete coordinatewise unordered signature partition summing to \(D=r^{2a}\), the exact packet waste equivalence, child incidence from row/column ports, and an abstract orbit packet budget.
2. [`IndependentTwoAdicMoments.lean`](https://github.com/laurajoyhutchins/eth-disproof-rust/blob/main/rust/lean_eth_reference/proofs/IndependentTwoAdicMoments.lean), merged in [#309](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/309), proves **13 independent finite-label sum lemmas**. For a matching represented by independently labelled edge endpoint pairs, it establishes \(\sum 2^{X_\gamma}=(D+1)^m\) and the exact rational mean \(((D+1)/D)^m\). For vertex symbol ports, it establishes \(\sum z^{C_s}=\prod_v(r-1+z^{d_v})\) and the normalized source factor \(\prod_v(1+(z^{d_v}-1)/r)\). The Lean bridge explicitly proves that the source's powers of **actual hit counts** are equal to the local products, including indivisible vertex-degree contributions.

Both checks passed at exact heads using pinned Lean 4.34.1 and Mathlib, with only standard Lean axioms and no proof placeholders. See [#306 verification](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43771961460) and [#309 verification](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43774480582).

**Those first two layers were not a kernel proof of the complete combined theorem.** The subsequent graph-vertex conditioning and matching independence lemmas are described below. The full combined normalized conditional potential, analytic exponential estimates, individual orbit fiber-size/copy-slot identities, and nonzero Cauchy/weighted-mode/precision/recursion correspondence remain unverified.

## Exact graph-vertex conditioning and matching uniformity (15 November 2026)

[Merged PR #314](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/314)
adds **12 Lean-kernel-checked lemmas** in two new source-shaped
modules, without introducing assumptions about the independence of
edges that share vertices.

**Partial graph-vertex port moments.**
[`IndependentTwoAdicConditionalMoments.lean`](https://github.com/laurajoyhutchins/eth-disproof-rust/blob/main/rust/lean_eth_reference/proofs/IndependentTwoAdicConditionalMoments.lean)
represents a partial assignment by `fixed : V → Option A`.
Each fixed vertex has one legal symbol, while each uncommitted
vertex has the entire finite alphabet. If `C_s` is the sum of
the **full degrees** of vertices assigned symbol `s`, then

\[
\sum_{\ell\text{ compatible with fixed}} z^{C_s(\ell)}
 =\prod_{v} \begin{cases}
 z^{d_v} & \text{fixed to }s,\\
 1 & \text{fixed to another symbol},\\
 r-1+z^{d_v} & \text{uncommitted}.
 \end{cases}
\]

This proves the conditional exponential **numerator** exactly,
including arbitrary parallel edges and fixed/free vertices. The
finite cardinality of compatible completions is also proved.
An edge-local partial pair-label factorization is separate and
does not by itself imply a source graph conditional matching identity.

**Real matching-endpoint distribution.**
[`IndependentTwoAdicMatchingGraph.lean`](https://github.com/laurajoyhutchins/eth-disproof-rust/blob/main/rust/lean_eth_reference/proofs/IndependentTwoAdicMatchingGraph.lean)
works with finite left and right graph vertices, an index type
`E` of selected matching edges, and injective endpoint maps
`left : E → L` and `right : E → R`.
The injections are necessary: distinct matching edges cannot
share an endpoint on the same shore. Other graph edges may
remain incident to the selected vertices, as they do not
alter the **vertex-label sample space**.

For any prescribed ordered edge-pair labeling `x : E → A×A`,
the compatible full graph-label fiber equals the product of
its left- and right-shore completion fibers. Lean proves
their common cardinality `c_E` is independent of `x`.
The stronger, fully weighted result holds for every
`w : (E → A×A) → ℚ`:

\[
\boxed{
\sum_{\ell\text{ on all graph vertices}}w(\ell|_E)
 =c_E\sum_{x\text{ on matching edges}}w(x).
}
\]

A separate cross-multiplied theorem equates the two **uniform
means**, avoiding division by zero at empty-alphabet
boundary cases. For a nonempty alphabet it yields ordinary
equality of normalized expectations. Thus the earlier exact
edge-local `2^X_gamma` matching moment genuinely transfers
to an actual bipartite graph with a matching, with **no
independence assumption on other graph edges**.

[Exact-head Lean 4.34.1 / pinned Mathlib workflow](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43793929792)
and [Rust CI](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43793929733)
passed. All 12 `#print axioms` receipts reported only
`propext`, `Classical.choice`, and `Quot.sound`.
None depended on an unproved placeholder.

**That was the source boundary at #314.** The arbitrary partial
matching moment and the one-vertex joint conditional-choice theorem
have subsequently been kernel-checked as described below. Their
source-wide explicit normalized exponential specialization and
analytic load bounds remain separate obligations.

## Matching moments after arbitrary partial assignments (#319)

[Merged PR #319](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/319),
commit `d524399d2852d473c220cd214497a261320d3566`,
proves the **actual source-graph matching moment after arbitrary
partial graph-vertex assignments**.

For every graph vertex, choose a finite set of permitted symbols.
For the source fixed/free labeling scheme this is a singleton or
the entire alphabet, but the theorem also covers empty permitted
sets. Let \(E\) be a selected matching whose left and right
endpoint maps are injective. If \(A_e\) is the permitted ordered
pair-label set at edge \(e\), then the kernel proves

\[
\sum_{\ell\text{ compatible}}2^{X_\gamma(\ell)}
= c_{\mathrm{unmatched}}\prod_{e\in E}
  \sum_{p\in A_e}2^{\mathbf1[p=\gamma]}.
\]

Here \(c_{\mathrm{unmatched}}\) is the exact product of
permitted-label counts at vertices not in the selected matching.
The proof first establishes that all permitted matching-edge
labelings have **the same number of full graph-label
completions**, then proves a weighted-sum transfer for an
arbitrary rational function of matching labels. It is not
limited to exponential weights. A cross-multiplied conditional
mean identity covers empty-completion boundary cases without
division by zero.

[Exact-head Lean verification](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43888791104)
and [Rust regression](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43888791085)
passed, with standard Lean axioms only. The endpoint
injectivity hypothesis must still be connected in Lean to
the source's specific greedy proper edge coloring.

## One sequential choice for a combined potential (#322)

[Merged PR #322](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/322),
commit `886906402d8b4cc4f1d7d2e63f22391f9b52a687`,
adds six more kernel-checked finite graph-labeling theorems.

Fix finite allowable label sets at all graph vertices. At a
chosen next vertex \(v\), every legal symbol \(x\) has the
same number of completions:

\[
c_v=\prod_{u\ne v}|A_u|,\qquad
|\mathcal C|=|A_v|c_v.
\]

The compatible full graph-labeling sum of **any rational
weight** \(w\) partitions exactly over the choice fibers
\(\mathcal C_x\). If \(|A_v|>0\) and \(c_v>0\), the
kernel proves existence of a symbol \(x\in A_v\) such that

\[
\boxed{
\frac{\sum_{\ell\in\mathcal C_x}w(\ell)}{c_v}
\le
\frac{\sum_{\ell\in\mathcal C}w(\ell)}{|\mathcal C|}.
}
\]

Apply it to \(w(\ell)=w_{\mathrm{matching}}(\ell)+
w_{\mathrm{ports}}(\ell)\). The **same** vertex-symbol
choice controls the sum, not necessarily each summand
separately. This is the deterministic finite
conditional-expectation choice step needed by a joint
labeling potential.

[Exact-head Lean verification](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43894147103)
and [Rust regression](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43894147132)
both passed with no unproved axioms.

**Exact boundary:** the weight functions in #322 are
arbitrary rational functions on graph vertex labels. A Lean
theorem still must define them as the original **explicit
normalized** matching-class and shore/coordinate/symbol-port
exponential sums, verify their full initial mean is 2,
connect the source edge-color matching, and derive the
analytical class/port bounds. A general nonincreasing
conditional-choice result does not by itself establish those
bounds or make the source's tensor recursion executable.

## Next acceptance frontier

This is a **worst-case simultaneous sufficient theorem**, but
it is not an all-depth or practical one. Further work must:

1. **Finish the source-specific theorem in Lean.** Both the
   arbitrary partial source graph **matching** moments and
   **port** moments, and a *generic one-choice combined
   conditional-expectation theorem*, are now kernel-checked.
   Instantiate the source's **explicit** matching/port
   exponential potential over actual graph vertices, prove
   the normalization and initial expected value 2, tie
   injective matchings to the source greedy coloring, prove
   analytic class and port bounds, and derive individual
   orbit multiplicities and packet copy-slot counts. Do not
   treat the finite conditional expectation lemma as a
   completed source tensor-contraction or complexity proof.
2. Extend exact *constructive* realization beyond the small
   `u128` reference using a reused arbitrary-precision Rust
   package, with a measured total labeling bit-cost receipt.
3. Replace the coarse all-\(O\)-orbit rounding error and large
   \(D\delta\log D\) sufficiency requirement if possible,
   without exhaustive large-input label enumeration.
4. Transfer the modified **nonzero** Cauchy deformation, weighted
   mode constraints, source packet coefficient identities, group
   factorization and precision to Lean and the Rust executor.
5. Produce one actual active source-defined recursive count with
   fully inclusive setup, arithmetic, node count, memory, and
   leaf work. No #SAT or ETH claim is discharged by this result.

See [packet construction issue #291](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/291)
and [complete contraction issue #258](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/258).
