# Collision packing by matching potentials

**15 November 2026. Status: a new, constructive mathematical packing argument with exact arithmetic checks.** This is not yet formalized in Lean and is not an executed two-adic contraction. It replaces one sufficient packing hypothesis, not the entire appendix recursion.

The target is OpenAI's [quantitative-contraction.tex](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex) at Git blob `51ba54efc29f51bbc0426f848003030da484f354`, particularly the lemma “Packing into packets.” The paper currently obtains

\[
\mathbb E\sum_\gamma(X_\gamma-M/D)^2\le2M\Delta
\]

and requires \(M\ge 2D^2\Delta\) to force uniform padded class loads. Here \(M\) is the edge count of the **current** bipartite tensor network, \(\Delta\) an upper bound on its maximum vertex degree, \(b=r^a\), \(D=b^2=r^{2a}\), and \(L=2^a\).

## Constructive replacement lemma

**Claim (matching-potential packing).** Let \(G=(U,V,E)\) be a finite bipartite multigraph with \(M\ge1\) edges, both-side maximum degree at most \(\Delta\ge1\). Let \(b\ge2\), \(D=b^2\), and let \(L\) divide the padded slot count as in the original construction. Suppose

\[
\boxed{
 M\ge D\left((2\Delta-1)\lceil\log_2D\rceil+L\right).
}
\]

Then there is a **deterministic polynomial-time** labeling of every left and right vertex by a symbol in \([b]\), such that, if \(X_\gamma\) is the number of edges with ordered label pair \(\gamma\in[b]^2\), the common padded load

\[
H_{\mathrm{pad}}=
 L\left\lceil\frac{\max_\gamma X_\gamma}{L}\right\rceil
\]

satisfies \(H_{\mathrm{pad}}\le3M/D\). Hence the original *subsequent* orientation-by-slot packet construction yields at most \(3M/L\) packets and, for each coordinate and symbol, at most \(3M/r\) actual ports on either side. If \(2L\le\Delta\), new packet vertices retain the original maximum-degree invariant, and each child has at most \(6M/r\) edges.

This **does not** independently prove the paper's interpolation/precision identities, child-shrink recurrence, or complexity theorem. It provides a replacement for the probabilistic collision-loading step of the packet lemma.

### Step 1. Color edges into matchings

Order the edges. Greedily assign each edge the first unused color at **both** endpoints. At most \(2\Delta-2\) colors are forbidden, so at most

\[
k=2\Delta-1
\]

colors suffice. Each color class \(E_c\) is a matching, including for multigraphs with parallel edges. Let \(m_c=|E_c|\), so \(\sum_cm_c=M\).

This elementary bound avoids relying on optimal bipartite edge-coloring. Kőnig's line-coloring theorem would improve \(k\) to \(\Delta\), with a separate polynomial-time coloring routine; that sharper constant is **not** part of the implemented checker.

### Step 2. Define an exponential potential

Label each vertex initially **independently uniformly** in \([b]\). For ordered pair \(\gamma\) and matching \(c\), let \(X_{\gamma,c}\) count the edges assigned that pair. Independence of *endpoints within a matching* gives

\[
\mathbb E\left[2^{X_{\gamma,c}}\right]
 =\left(1+\frac1D\right)^{m_c}.
\]

Define the normalized potential

\[
\Phi=
\sum_{\gamma\in[b]^2}\sum_{c=1}^k
 2^{X_{\gamma,c}}
 \left(\frac{D}{D+1}\right)^{m_c}.
\]

Each summand has expectation one; therefore

\[
\mathbb E\Phi=Dk.
\]

The matching separation is essential. For two disjoint edges, binary vertex labels, and one ordered pair, the exact sum of \(2^X\) over all 16 assignments is 25, matching \((5/4)^2\). If the two edges share one row vertex, the sum over eight assignments is 13, not the independent matching value of 25/2.

### Step 3. Derandomize with exact conditional expectation

Process vertices in a fixed order. For each candidate label of the next vertex, evaluate

\[
\mathbb E[\Phi\mid\text{assigned vertex labels}].
\]

In a matching, still-unassigned endpoints of different edges are disjoint. Hence this conditional expectation factors as

\[
\sum_{\gamma,c}
\left(\frac{D}{D+1}\right)^{m_c}
\prod_{e\in E_c}(1+q_{e,\gamma}),
\]

where \(q_{e,\gamma}\) is the conditional probability that the edge's endpoint labels equal \(\gamma\). Its only possible values are \(0,1/b,1/D,1\).

The estimator is exactly computable with **rational integer arithmetic**, without enumeration of assignments. Multiplying by the common denominator \((D+1)^M\) gives an integer:

\[
\widehat\Phi=
\sum_{\gamma,c}(D+1)^{M-m_c}
\prod_{e\in E_c}(D+Dq_{e,\gamma}).
\]

Each factor is one of \(D,D+1,D+b,2D\). Comparing candidate labels by \(\widehat\Phi\) is exact. Since the current conditional expectation is the mean over the next label choices, selecting a minimizer never increases it. After all vertices are assigned,

\[
\Phi\le Dk.
\]

All numerators and denominators have \(O(M\log D)\) bits, and there are polynomially many candidates and terms when \(b,D\) are polynomial in \(M\). Thus this is a deterministic polynomial-time algorithm under the original appendix's polynomial bound on the number of labels. An implementation must use arbitrary-precision integers; wrapping fixed-width arithmetic would invalidate the certificate.

### Step 4. Control every class, not only average load

Fix a class \(\gamma\). Apply the arithmetic-geometric mean inequality to its \(k\) positive terms in \(\Phi\):

\[
\left(
\frac{2^{X_\gamma}}{(1+1/D)^M}
\right)^{1/k}
\le\frac1k\sum_c
\frac{2^{X_{\gamma,c}}}{(1+1/D)^{m_c}}
\le \frac{\Phi}{k}\le D.
\]

Therefore

\[
2^{X_\gamma}\le D^k(1+1/D)^M,
\]

or equivalently

\[
X_\gamma\le
k\log_2D+M\log_2(1+1/D).
\]

The elementary bound \(\ln2>2/3\), together with \(\ln(1+x)\le x\), gives

\[
\log_2(1+1/D)<\frac{3}{2D}.
\]

Since \(k\le2\Delta-1\), the stated sufficient inequality implies

\[
k\log_2D+L\le\frac MD.
\]

It follows that

\[
H_{\mathrm{pad}}
\le X_{\max}+L
<\frac{3M}{2D}+\frac MD
=\frac{5M}{2D}<\frac{3M}{D}.
\]

In particular, \(H_{\mathrm{pad}}D/L\le3M/L\). The original packet construction needs only equal, \(L\)-divisible class loads, not a second-moment certificate. Every fixed coordinate symbol occurs on the row (or column) side in exactly \(D/r\) padded classes; its real port count is bounded by \(H_{\mathrm{pad}}D/r\le3M/r\).

The source's orientation-by-slot grouping, canonical lifts and tensor identities remain unchanged under this stronger labeling argument.

## How much is gained?

The old first inequality is \(M\ge2D^2\Delta\). The new sufficient inequality is

\[
M\ge D\left((2\Delta-1)\lceil\log_2D\rceil+L\right).
\]

For fixed \(L\), this replaces the leading \(D^2\Delta\) cost with \(D\Delta\log D\). For the source's \(r=64\), hypothetical \(u=1\), \(a=2\), \(L=4\), \(D=2^{24}\), and a **certified** degree cap \(\Delta=8\):

| Condition | Minimum numerical root size |
|---|---:|
| Original collision condition | \(2^{52}=4{,}503{,}599{,}627{,}370{,}496\) edges |
| New matching-potential sufficient condition | \(2^{24}(15\cdot24+4)=6{,}106{,}906{,}624\) edges |
| Further theoretical optimum using \(\Delta\) matchings | \(2^{24}(8\cdot24+4)=3{,}288{,}334{,}336\) edges |

The final row uses an additional line-coloring theorem and is **not** checked by the conservative Rust implementation. Even the improved numerical root size is far too large to be useful as a complete counting run, and the hypothetical \(u=1\) violates the paper's \(u\ge\lambda^{4/5}\) asymptotic regime. With the paper's \(\Delta=\lceil s^{9/10}\rceil\), the new inequality also remains impossible for realistic-size inputs. The appendix's original \(\varepsilon\), deeper-degree invariants and massive leaf threshold are untouched.

For the *changed* packing lemma, the previous \(16r^8\) floor from the old \(D^2\Delta\) inequality is **not** a universal requirement. It was conditional on the old lemma.

## Bounded executable labeling reference

The separate `two_adic_matching_labels::construct_bounded` Rust routine implements
the **actual deterministic labeling algorithm** on small bipartite multigraphs:
greedy proper edge coloring, exact conditional-expectation comparisons with
one integer denominator, and a final certificate containing the labels,
color classes, class loads and potential numerator. No random sampling or
floating-point estimates are used. Parallel edges and shared endpoints are
tested. The code refuses fixed-width overflows and intentionally limits
the graph/alphabet sizes. It is a correctness reference, **not** the
unrestricted polynomial-time implementation justified by the proof; that
version needs a standard arbitrary-precision integer dependency.

A second bounded reference, `two_adic_packet_layout::pack_bounded`,
now implements the source's subsequent **structural packet layout**:
pad every ordered label pair to a common multiple of `L`; group
coordinatewise unordered symbol pairs; use each slot bit for the
orientation at unequal coordinates and the copy index at equal
coordinates. It checks every real edge is used exactly once, that
both ends occupy the same slot, that per-coordinate ports are bounded,
that packet count is at most `3M/L`, and that old and new vertex degree
caps hold. It intentionally refuses actual overloaded class layouts.

These witnesses use bounded graphs and checked integers. Neither
the layout nor the labeling reference constructs packet tensor
entries, signed coefficient modes, or an actual two-adic recursion;
the paper's precision schedule and complexity theorem remain open.

## Executable arithmetic and proof obligations

`RootPackingAudit.matching_potential_required_edges()` computes the new sufficient threshold using checked \(u128\) arithmetic, and `matching_potential_packing_holds()` separately checks \(2L\le\Delta\). This is a numerical check, not a verified constructed labeling. The `appendix-packing` CLI always returns an unsupported-recursion receipt; its field `matching_packing_arithmetic_holds` is not a proof of a full recursion.

The next gates are specific:

1. Formalize the matching decomposition, exact conditional estimator and final load bound as a Lean lemma, with no unproved existence hypotheses.
2. Implement the arbitrary-precision conditional minimizer, generate actual vertex labels, then verify all \(D\) pair loads and the source's fixed-slot packet assignment on adversarial graphs.
3. Replace only the original packing invocation; verify all deeper input degrees, new packet ports, child edges, valuation/precision and coefficient identities without changing the meaning of the source algorithm.
4. Recompute the complete recurrence and measure actual end-to-end counting cost. A labeling improvement is not an ETH disproof or a speedup in isolation.

[Previous packing obstruction](root-packing-feasibility.md) · [Recursion identity](two-adic-recursion.md) · [Full cost model](cost-model-and-benchmarks.md) · [Execution issue #258](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/258)
