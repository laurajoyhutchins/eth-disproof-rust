# Depth-sensitive paper support and the Sudoku cell-parameter obstruction

**Status:** conditional improvement to the *support-summation exponent*, not a proof of a non-refusing solver. The paper bit-work acceptance test remains **RED**. Implementation correspondence for the symbolic inequalities is `reference/paper_depth_sum.py`; the separate three-copy cut is `reference/sudoku_three_copy_cut.py`.

## 1. Do not take the worst depth and multiply by the number of levels

Set \(s\) to the network edge-size parameter, \(\lambda=\lceil\log_2 s\rceil\), \(U=\lfloor\lambda/131072\rfloor\), \(\rho=3/32\). There are \(D=1+\lfloor\log_2 U\rfloor\) active depths when \(U\ge1\). The literal source schedule gives

\[
 u_d=\left\lfloor U/2^d\right\rfloor,\quad
 a_d=2\sum_{j=0}^d u_j\le4U,\quad
 M_d\le\rho^d s.
\]

The preceding global-mode-support lemma established for every *eligible center* at depth \(d\) the **conditional** bound

\[
\frac{K_{d,i}p_{d,i}}{s^2}\le
R_d:=\frac{3\rho^d(37+8(a_d+1))}{2^{u_d}}
+\frac{192\rho^{2d}}{u_d}.
\]

The positive-weight colored-partition bound gives

\[
\log_2 A_{d,i}<4\sqrt{K_{d,i}p_{d,i}}
\le4s\sqrt{R_d}.
\]

Formerly, the composed proof used \(D\max_d\sqrt{R_d}\). That upper bound is correct but wastes the geometric decrease in child edges. The recurrence needs \(\sum_d\sqrt{R_d}\), not the maximum times the number of depths.

## 2. Sum the two terms, with an explicit uniform constant

Write \(x_d=2^d\), \(y_d=U/x_d\); at active depths \(y_d\ge1\). We have

\[
 u_d=\lfloor y_d\rfloor\ge y_d-1,\qquad
 u_d\ge y_d/2,\qquad \rho\le1/4.
\]

For the first term \(A_d=3\rho^d(37+8(a_d+1))2^{-u_d}\), since \(37+8(a_d+1)\le45+32U\le77U\),

\[
 \sqrt{A_d}\le
 \frac{\sqrt{462}}{\sqrt U}\,y_d\,2^{-y_d/2}.
\]

The positive \(y_d\) halve from one depth to the next, so there is at most one \(y_d\) in every dyadic interval \([2^j,2^{j+1})\). Consequently

\[
 \sum_d y_d2^{-y_d/2}
 \le\sum_{j\ge0}2^{j+1}2^{-2^{j-1}}<8,
\]

and \(\sum_d\sqrt{A_d}<8\sqrt{462}/\sqrt U<172/\sqrt U\).

For the second term, \(B_d=192\rho^{2d}/u_d\),

\[
 \sqrt{B_d}\le\frac{\sqrt{384}}{\sqrt U}
 \left(\frac{\sqrt2}{4}\right)^d,
\]

so \(\sum_d\sqrt{B_d}<31/\sqrt U\).

The symbolic helper may cap the exponent \(u_d\) at \(2\operatorname{bitlength}(\lambda)\) to avoid allocating gigantic denominators. This **enlarges** \(A_d\). At capped depths \(2^{u_{\rm cap}}\ge U^2\), so their additional first-term square-root sum is at most \(2\sqrt{231}/\sqrt U<31/\sqrt U\). Splitting capped and uncapped levels preserves the same bound with room to spare:

\[
\boxed{\sum_{d:u_d\ge1}\sqrt{R_d}<\frac{256}{\sqrt U}.}
\]

For integer ceilings \(\alpha_d=4\lceil\sqrt{K_{d,i}p_{d,i}}\rceil\), we therefore have

\[
\boxed{\sum_d\alpha_d<\frac{1024s}{\sqrt U}+4D
=O\!\left(\frac{s}{\sqrt{\log s}}\right).}
\]

`summed_paper_support_exponent` uses \(\lfloor\sqrt U\rfloor\) for an integer-only, deliberately looser bound. Tests compare literal schedule ratios, exact rational formulas, and integer-square-root upper ceilings. Testing finite inputs does not substitute for the dyadic proof above. The first active \(U=1\) has \(R_0=567/2>1\), so this asymptotic statement promises no practical finite-size win there.

## 3. Consequence for the *conditional* whole-frame recurrence

The existing composed frame model charges at most \(2^{O(\alpha_d)}\) center/factor arithmetic and child work, up to polynomial prefactors, with terminal and early-numeric-fallback leaves of at most \(O(s/\sqrt\lambda)\) Boolean edges. With the **same outstanding source, oracle, memory and non-refusal premises as before**, summing the actual depth-dependent exponents rather than multiplying a uniform maximum by \(D\) gives the stronger *counterfactual* network-time expression

\[
\boxed{\log_2 T(s)=O\!\left(\frac{s}{\sqrt{\log s}}\right).}
\]

This is **not an established bit-time upper bound for the production code**. It is a valid conditional mathematical composition of the previously stated assumptions. In particular, the current finite `ModeLimits`, leaf limits, general Python callbacks and unclosed memory contracts still prevent certification. The numerical `whole_frame_recurrence.py` remains a skeleton rather than a theorem certificate.

## 4. This still does not establish subexponential time in Sudoku *cells*

For box order \(b=2^k\), the direct Boolean reduction has side \(n=b^2\), cells \(N=b^4=2^{4k}\), digit width \(t=2k\), and exactly

\[
 M=3Nt=6kN,\qquad \lambda=\lceil\log_2 M\rceil\le10k.
\]

Consequently the displayed network **upper-bound formula** becomes

\[
O(M/\sqrt{\log M})=O(N\sqrt{\log N}),
\]

which is **not** an \(o(N)\) exponent. More explicitly, the scale of that upper-bound expression compared with \(N\) grows without bound:

\[
\left(\frac{M}{N\sqrt\lambda}\right)^2
=\frac{36k^2}{\lambda}\ge\frac{18}{5}k\longrightarrow\infty.
\]

This says **nothing about a lower bound on the actual algorithm's running time**. It shows that even the sharpened *upper-bound argument* cannot justify \(2^{o(N)}\) through this reduction. For a network-time bound \(O(s/\sqrt{\log s})\), a hypothetical reduction \(s=O(N(\log N)^\delta)\) would transfer automatically if \(\delta<1/2\), not for \(\delta=1\).

### The existing three-copy architecture is already wire-optimal under its interface restrictions

The `DirectNetwork` reduction connects each cell separately to its row, column and box constraint using disjoint binary-wire digit copies. Assume **each interface independently must distinguish all \(n\) digits, with no other cell-to-unit side channel**. Injectivity then requires at least \(\lceil\log_2 n\rceil\) Boolean wires for *each* of the three interfaces by the pigeonhole principle. For \(n\ge2\),

\[
 \boxed{M\ge3N\lceil\log_2 n\rceil},
\]

and the current direct reduction **attains equality**. The companion executable helper checks this against the actual dimension formula and correctly handles the degenerate \(n=1\) padding. This lower bound is deliberately **restricted to this particular three-independent-copy interface architecture**. It does **not** rule out a new weighted tensor representation, nonbinary bonds, shared information, or a genuinely different encoding.

## 5. Acceptance implications

- This increment strengthens the **conditional** rate used by `reference/cell_rate_transfer.py` from `(alpha,beta)=(1/4,1)` to `(1/2,0)` and updates the independent theorem gate's explanation. It **does not** change either gate's refusal status.
- The now-sharp target for a cell-based proof is \(\log_2 T=o(s/\log s)\) for \(s=\Theta(N\log N)\), requiring a further \(\sqrt{\log s}\) savings over the displayed \(O(s/\sqrt{\log s})\) bound. Improved factor support, cross-mode cancellations or a different encoding would need independently proved guarantees.
- A non-refusing source-level bit-work theorem, and any claimed ETH consequence, remain unproved. Keep `research_acceptance/test_complete_bit_recurrence.py` **RED**.
