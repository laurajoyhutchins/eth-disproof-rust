# Quantitative measurement witness: use selector rows, project the space

The previously established identity \`G=B^T W B\` proves that
**restricted exceptional selectors** and the projected Gram matrix
span the same rational row space. This note closes an important
*existential quantitative* gap: one can choose an independent subset
of the ORIGINAL integral selector rows, preserving the exact
measurement row space **and** the source's literal integer L1
bound. One does not need to bound the L1 of the primitive rows
produced by Gram RREF itself.

It does not remove capacity refusal from the existing selector
enumerator, prove the entire source transfer total, or establish
non-exponential exact counting.

## 1. Sparse selector subset preserves the numerical norm

Let \(\mathcal S\) be the original exceptional product-eigenvector
selector set for the actual \(r,Q,R\) spectral operator, with
\(c=|\mathcal S|\le D=r^{2Q}\). Each integer selector \(u\) has
entries in \(\{-1,0,1\}\). After restricting to one occupied
incidence-label copy, each label occurs at most once, so the
selector row \(B_u\in\mathbb Z^{|S_g|}\) satisfies

\[
 \|B_u\|_1
 \le \#\{\text{occupied labels in this copy}\}
 \le D.
\]

The last inequality holds even if multiple distinct labels refer
to the same variable. Copies were introduced precisely to ensure
that each label appears at most once in a copy.

Select a maximal linearly independent subset of these **original**
rows using exact incremental elimination. This yields a matrix
\(\widehat B\) of rank \(k\) with

\[
  \operatorname{rowspace}_\mathbb Q\widehat B
   =\operatorname{rowspace}_\mathbb Q B
   =\operatorname{rowspace}_\mathbb Q G,
  \qquad
  k\le c,\qquad
  \max_{b\in\widehat B}\|b\|_1\le D.
\]

With \(h\) occupied-label copies and \(r\) groups per center,
this basis uses at most \(rhc\) rows, just as the uncompressed
selector construction does. In particular, basis selection **cannot
worsen** the original numerical row-count or row-L1 certificate.

The executable algorithm in
\`src/non_exponential_sudoku/eth/selector_subbasis.py\` retains
*original rows* and recomputes the new actual \(\tau,D_\text{row}\).
Its Fraction pivot computations have determinant-ratio entries:
for rank \(k\), source maximum L1 \(L\), a conservative
numerator/denominator bound is

\[
 O\bigl(k[\log_2(L+1)+\log_2(k+1)]\bigr).
\]

The selection algorithm is polynomial in the number of explicitly
supplied rows, their width, and input coefficient bit lengths.
It does not need a large RREF-derived integer basis.

A small **counterexample** demonstrates why the distinction matters.
The source integer rows

\[
 B=\begin{pmatrix}
 -1&-1&-1&0\\
 -1&0&1&-1
 \end{pmatrix}
\]

have maximum L1 norm **3**. Their primitive integral RREF is

\[
 \begin{pmatrix}1&0&-1&1\\0&1&2&-1\end{pmatrix},
\]

whose second row has L1 norm **4**. This is a general
linear-algebra counterexample, **not** an assertion that the
particular small spectral construction realizes this matrix.

## 2. Prove the Step-5 exceptional selector count without enumerating c

The exceptional selector count in the production source is

\[
 c=\sum_{j\notin I}\binom Qj a_-^j a_+^{Q-j},\qquad
 a_-=\frac{r(r-1)}2,\quad a_+=\frac{r(r+1)}2.
\]

Since \(a_-+a_+=r^2\), dividing by \(D=r^{2Q}\)
identifies \(c/D\) with a binomial tail probability for

\[
 X\sim\mathrm{Binomial}(Q,p),\quad p=\frac{r-1}{2r}.
\]

The actual interpolation interval \(I\) consists of \(R\)
consecutive integers centered (with a one-integer floor) at \(Qp\).
Under the audited hypotheses \(R\ge32\) and \(6R\le Q\),
the interval lies strictly inside \([0,Q]\). Each excluded
index deviates from \(Qp\) by at least \((R-1)/2\).
Hoeffding's inequality gives

\[
 \frac cD
 \le 2e^{-(R-1)^2/(2Q)}
 \le 2e^{-R^2/(8Q)}
 \le 2^{1-\lfloor R^2/(8Q)\rfloor}.
\]

The final inequality uses \(e^{-x}\le 2^{-x}\)
for nonnegative real \(x\), and the bound
\((R-1)^2/2\ge R^2/8\) for \(R\ge2\).

The literal manuscript sufficient inequality

\[
 R^2\ge2048Q\nu,\qquad \nu=\lceil\log_2\lambda\rceil
\]

therefore ensures

\[
 \boxed{c/D\le2^{1-256\nu}}.
\]

This bound requires only small integer parameter arithmetic.
There is **no** need to materialize \(D\), \(c\), or a
symbolic \(n\)-variable CNF.

## 3. Compose with the balancing lemma and row-count requirement

Let \(M\) be total literal incidences, \(n\) the Boolean
variable count, \(h\) the maximum label-copy multiplicity,
\(\lambda=\lceil\log_2n\rceil\), and assume the source
balancing lemma has supplied its **independent** guarantee

\[
 hD\le2M.
\]

A maximal independent selector subbasis across all copies and
groups then uses at most

\[
 \#\text{rows} \le rhc
 \le 2rM(c/D).
\]

The manuscript needs
\(\#\text{rows}\le 2n/(r\lambda)\).
It is sufficient to establish

\[
 (r^2\lambda M/n)(c/D)\le 1.
\]

Under the audited conditions \(M\le3n\),
\(r^2\le\lambda\) and \(\lambda\le2^\nu\),
the left-hand side is at most

\[
 3\cdot 2^{2\nu}\cdot 2^{1-256\nu}
 =3\cdot2^{1-254\nu} < 1.
\]

Therefore, for **every instance satisfying the paper's
literal Step-5 hypotheses and the actual balancing multiplicity
bound**, there EXISTS a selector subbasis representing the same
projected measurement directions and satisfying **both**
quantitative requirements:

\[
 \boxed{
 \#\text{rows}\le\frac{2n}{r\lambda},
 \qquad
 \max\|b\|_1\le D.
 }
\]

This is a universal statement about the source spectral
representation and the independently stated balancing premise,
not an extrapolation from small experiments.

The certificate is implemented in
\`reference/eth_quantitative_selector.py\`. For the genuinely
Step-5-admitted symbolic family in
\`docs/eth-paper-lean-admission.md\`,
\(\lambda=2^{34},\nu=34,r=113,Q=3{,}947{,}580,
R=524{,}288\), and it yields the explicit dyadic
bounds

\[
 c/D \le 2^{-8703},\qquad
 (r^2\lambda M/n)(c/D)\le 3\cdot2^{-8635}.
\]

Neither the virtual \(n\) nor \(D\) is allocated.

## 4. Cost and implementation boundary

The **selector subset** can be found constructively by
enumerating the at most \(c\le D\) exceptional selectors and
performing incremental rational rank tests on their transferred
integer rows. Every original entry has \(\le D\) magnitude,
so rational intermediate bit lengths are bounded by
determinants of rank at most \(\min(c,g)\).
The total arithmetic work and bit storage are polynomial in
\(c,g,Q,\log D\) and the number of occupied copies.
Under the manuscript's dimension condition
\(D^{128}\le2n\) and bounded incidence \(M\le3n\),
this is **polynomial in \(n\)** in an abstract bit-machine model.
It may be astronomically expensive for the first admitted \(n\).

**What is not established:**

- The *particular primitive Gram basis currently returned by
  \`projected_group_basis\`* is not guaranteed to obey
  \(\max\|b\|_1\le D\). The sparse selector subbasis is an
  alternative basis, not a statement about that output.
- \`prune_selector_design\` starts with already enumerated
  selector rows. Existing \`ConstructionLimits\` and
  \`BalanceLimits\` can still refuse before it can run.
  This PR does **not** silently bypass resource caps or switch
  strict paper defaults.
- The full source-level balancing and transfer implementation,
  all center certification and witness-solving bit costs,
  interpolation, recursive contraction, and the claimed
  non-exponential worst-case counting theorem remain separate
  proof obligations.
- The dyadic certificate assumes the independently verified
  incidence-balancing lemma's \(hD\le2M\); it does not
  generate schedules or count arbitrary unrelated matrices.

The appropriate next engineering target is an **uncapped
mathematical reference path with an explicit worst-case bit-cost
contract**, or an implicit selector-basis extraction algorithm
that avoids even enumerating all \(c\) selector rows while
preserving this stronger numerical certificate.
