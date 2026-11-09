# Source-level coefficient height for the implicit spectral auxiliary

**Status:** unconditional rational-height bounds for the concrete
\`construct_implicit_auxiliary\` kernel, \`ImplicitAuxiliaryDesign.row_at\`,
\`exceptional_projector_at\`, and the occurrence transfer. This is **not**
a totality theorem for the full auxiliary constructor, the paper's
balance-and-measurement admission, nor the recursive counting algorithm.

Executable symbolic proof reference:
\`reference/eth_implicit_height.py\`; exact source-correspondence tests:
\`tests/eth/test_implicit_height.py\`.

## 1. Bound one coefficient without constructing D = r^(2Q)

The source permits \(r\ge2,\ Q\ge1,\ 1\le R\le Q+1\).
Its interpolation interval is
\(\{a,a+1,\ldots,a+R-1\}\subseteq\{0,\ldots,Q\}\), and the
source builds

\[
 f(T)=\sum_{k=0}^{R-1}
 (-1)^a\frac{(-2)^k}{k!}
 \prod_{i=0}^{k-1}(T-a-i).
\]

Put \(L=(R-1)!\), \(F=Q!\), and
\(C=R\,[2(Q+1)]^{R-1}\). For each integer \(j\in[0,Q]\),
\(Lf(j)\) is an integer of magnitude at most \(LC\), since every
factor \(|j-a-i|\le Q\). This bound uses no evaluation over the
\(r^{2Q}\) auxiliary coordinates.

The source's Hamming-weight Walsh coefficients are Fourier averages
of these \(Q+1\) evaluations. Each has denominator dividing
\(2^Q L\) and scaled numerator magnitude at most \(2^Q LC\).
The entry \`auxiliary.kernel[diagonals][unchanged]\` is a sum
of at most \(2^{\mathrm{diagonals}}\le2^Q\) Walsh coefficients.
Therefore every rational kernel entry \(m\) satisfies

\[
  (2^Q L)m\in\mathbb Z,\qquad
  |(2^Q L)m|\le2^{2Q}LC.
\]

This applies to all \(O(Q^2)\) entries computed by the
*actual* \`_walsh_by_weight\` and implicit kernel loop, not
a hand-selected spectral matrix.

## 2. Bound all coefficients of a source swap row

The implementation returns

\[
 P_{u,w}(T)=\mathbf1_{u=w}
   +m\left(\prod_{h\in S}(1-T/h)-1\right),
\]

where \(S\subseteq\{1,\ldots,Q\}\), \(|S|\le R-1\).
For a disallowed swap pattern it returns the identically zero
polynomial. Since the indices \(h\) are distinct, their product
divides \(F=Q!\). Each coefficient of
\(F(\prod_{h\in S}(1-T/h)-1)\) is an integer of absolute value
at most \(2^RF\).

Consequently all coefficients of every permitted row have the
**same universal positive denominator**

\[
 H=2^Q (R-1)!\,Q!,
\]

and the corresponding scaled integer numerator has magnitude at most

\[
 H+2^{2Q+R}(R-1)!\,Q!\,C.
\]

This is true simultaneously for *all* \(D^2\) conceptual entries,
although evaluating the full dense matrix may require \(D^2\) work.
It is a bound on an arbitrary **queried** coefficient, not
a claim that all entries are cheap to store.

Write

\[
\begin{aligned}
  h_L&=(R-1)\lceil\log_2 R\rceil,\\
  h_F&=Q\lceil\log_2 Q\rceil,\\
  h_C&=\lceil\log_2 R\rceil+
       (R-1)(1+\lceil\log_2(Q+1)\rceil).
\end{aligned}
\]

The executable ceilings, requiring only integer logarithms and
products and **no factorials, D, or row allocation**, are

\[
\begin{aligned}
 \operatorname{bits}(\operatorname{den}P_{u,w,j})
   &\le Q+h_L+h_F+1,\\
 \operatorname{bits}(\operatorname{num}P_{u,w,j})
   &\le\max(Q+h_L+h_F,\,
      2Q+R+h_L+h_F+h_C)+2.
\end{aligned}
\]

Thus all queried rational coefficient heights are
\(O(Q\log(Q+1)+R\log(Q+1))\), with no dependence on the
virtual dimension \(D=r^{2Q}\) except the cost of indexing labels.

The **restricted exceptional projector** is separately bounded.
In \`exceptional_projector_at\`, the full coefficient sum and the
interval-selected sum of \((1+z)^{s}(1-z)^{t}\) have respective
absolute numerators at most \(2^Q\).
The returned projector entry has denominator dividing
\(2^{s+t}\), so its reduced numerator and denominator bit
lengths are bounded by \(Q+2\) and \(Q+1\), respectively.

## 3. Actual occurrence transfer and every center

The occurrence transfer uses at most \(\ell\) occupied coordinate
labels in a copy, with \(\ell\) the original number of literal
occurrences. Each of its \((e,\text{literal},v)\) coefficients
is a sum of at most \(\ell\) row polynomials with the **same**
denominator \(H\), and has degree at most \(R-1\).
Hence its numerator-height bound increases by at most
\(\lceil\log_2(\ell+1)\rceil+1\) bits, while the
denominator-height bound is unchanged.

The expanded replacement has at most

\[
 K\le n\ell R
\]

stored rational polynomial coefficients, since every occurrence
provides \(n\) polynomials with at most \(R\) dense coefficients.
All actual construction centers are the integers
\(1,\ldots,Q\), so their input bit lengths are at most
\(\operatorname{bits}(Q)\).

\`implicit_deformation_output_height\` composes these structural
source bounds with the independently proved
\`universal_deformation_output_height\` lemma, obtaining a
uniform bound on all final coefficients of \(H(t+z)\) **without**
generating the replacement array or enumerating the Boolean cube.

Under the manuscript's *conditional* main-body parameter definitions,
\(Q=O(\log n)\) and \(R=O(\sqrt{\log n})\), so
individual auxiliary coefficients have
\(O(\log n\log\log n)\) bit length. For bounded-occurrence
3-CNF with \(\ell\le3n\), the composed **final output**
coefficient-height expression is polynomial in \(n\).
This is an input-size statement, **not** an algorithmic worst-case
time or non-refusal theorem.

## 4. Which construction costs this controls, and which it does not

The projector-mode source builds only a \((Q+1)^2\)
Walsh kernel table, rather than a dense \(D^2\) operator.
Its interpolation, differences, and kernel loops use polynomially
many rational and integer operations in \(Q,R,\log r\);
their operand bit lengths stay polynomial by the denominator
invariants above. A *single* \`row_at\` query takes an \(O(Q)\)
label scan and polynomial multiplication of at most \(R-1\)
linear factors. An \`exceptional_projector_at\` query loops
through at most \(Q R\) binomial terms. With schoolbook big-integer
arithmetic, these **individual oracle computations** have
polynomial bit cost in those source parameters. There is no
hidden \(D\)-entry loop in these queried functions.

This does **not** establish the whole construction's
polynomial cost or totality:

- Projector restriction forms exact Gram matrices and performs
  rational RREF for occupied labels. Its *intermediate* bit and
  storage costs need separate source-level accounting.
- The balancing implementation enumerates \(r^Q\) candidate
  schedules; the paper's \(D^{128}\le2n\) hypothesis makes
  that at most \((2n)^{1/256}\), but the current finite
  \`BalanceLimits\` still refuse large cases.
- The strict \`construct_paper_bounded_designs\` entrypoint
  currently defaults to **selector** measurements, not the
  projected rowspace path proved compact here. Enumerating those
  selectors has different work/memory costs.
- Even polynomial-cost access to any requested spectral entry
  does **not** bound the number of requested entries, tensor
  bond rank, factor elimination work, interpolation memory,
  or recursive oracle calls.
- The literal paper admission remains inactive at practically
  constructible sizes. Nothing in this note certifies a
  generated instance as satisfying the full admission conditions.

## 5. Independently executed verification

The source tests compare exact kernel entries, all queried row
polynomial coefficients and exceptional projector entries against
the symbolic bounds. A small implicit operator is compared with
the fully materialized dense operator. Actual projector-based
balanced constructions are checked through **every** transferred
replacement coefficient, at **every** generated interpolation center.
At small n, the full deformation is independently evaluated over
the Boolean cube, and the actual output bit lengths are compared
against both the expanded-input lemma and the symbolic bound.
A high-dimensional source query additionally exercises
\`row_at\` and \`exceptional_projector_at\` without allocating D.

The tests distinguish valid source parameter shapes, paper
admission, mathematical output size and implementation capacity.
The theorem-acceptance test remains **RED** because a complete
source-level bit-work and storage recurrence is still missing.

Reproduce:

\`\`\`bash
python -m mypy --strict reference/eth_implicit_height.py
PYTHONPATH=src:. python -m pytest -q tests/eth/test_implicit_height.py
\`\`\`

**Verified execution (2026-11-09):** GitHub Actions
[run 42719959938](https://github.com/laurajoyhutchins/nonexp-sudoku/actions/runs/42719959938)
passed 10 exact tests, strict typing of the proof module, and strict
production typing across 79 source files. The high-dimensional
source-oracle fixture has \(r=17,Q=12,R=3\) and conceptual
\(D=17^{24}>10^{25}\); it actually evaluates \`row_at\` and
\`exceptional_projector_at\` with a certified uniform
row-numerator ceiling of 93 bits, and never allocates a
\(D\)-entry array. The other fixtures include exact dense-vs-implicit
row equality, source kernel and projector checks, and
actual balanced transferred replacements checked at every emitted
center against independently evaluated full Boolean-cube
deformation polynomials. All are finite source-correspondence
checks, not admission certificates.
