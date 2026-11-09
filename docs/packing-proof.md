# Packing lemma: implementation-to-proof correspondence

**Scope.** This note establishes the packet-packing part of the conditional
Boolean-tensor contraction theorem for the code in `core/packing.py`, under
its **stated numerical hypotheses**. It does not establish that the paper
schedule becomes active on constructible Sudoku boards, or that mode
elimination, exact arithmetic, resource admission, and the leaf solver attain
the advertised total bit-complexity and non-refusal claims.

Primary source: OpenAI, *The Exponential Time Hypothesis is False* (2026),
Appendix D, “Parameters and collision packing,” Lemma “Packing into
packets.” See
[the source proof](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex).

## 1. What is being minimized

Let the bipartite multigraph have `M` *distinguishable* edges, left and
right endpoints `l(e)` and `r(e)`, maximum degree `Delta`. Put
`R=r**a`, `D=R**2`, `L=2**a`. Assign each vertex independently and
uniformly a full label in `[r]^a`, identified with `[R]`. If `X[g,h]`
is the number of edges whose endpoint labels form `(g,h)`, define

\[
F=\sum_{g,h}(X[g,h]-M/D)^2
 =\sum_{e,f}\mathbf 1[\ell(e)=\ell(f)]
                  \mathbf 1[\rho(e)=\rho(f)]-M^2/D.
\]

The second expression uses **ordered** edge pairs and includes parallel
edges and the diagonal. Its conditional expectation, given some vertex
labels, is exact: for distinct vertices on one side, label equality has
probability `1/R` if at least one remains unassigned, otherwise it is
`0` or `1`; identical vertices agree with probability `1`. Expectations
for the left and right sides multiply because labels are independent.

### Greedy left-label score

Assign all left vertices first. When the next vertex `v` has degree
`d_v`, compare it with each previously assigned left vertex `w`, of
degree `d_w`. Let `q(v,w)` be the number of **ordered endpoint pairs**
`(e,f)` with `e` incident to `v`, `f` incident to `w`, and the same
right endpoint. The conditional probability of right-label agreement is

\[
 q(v,w) + (d_vd_w-q(v,w))/R.
\]

The candidate-dependent part of `E[F]` is twice the sum of this number
over previously labeled `w` with `label(w)=candidate`. All other terms
are independent of the candidate. Multiplying scores by the positive
constant `R/2` yields precisely the production score

```
len(vertex.ports) * len(previous.ports) + (R - 1) * shared
```

in `balanced_labels`, where `shared` is counted using the right-endpoint
histograms. An unused label has score zero, which is minimal since all
scores are nonnegative. The `spread` tie-break chooses a fresh label by
an invertible triangular map on `(Z/rZ)^a`; all first `R` choices are
distinct. Once all full labels are used, minimizing the sparse scores
over all occupied labels minimizes the full conditional expectation.
For `numeric`, a single unused label suffices because every unused
label has the same zero score; this remains true even if the numeric
tie-break has previously reused labels at a zero-score step.

### Greedy right-label score

Once all left labels are fixed, let `h_v(g)` count edges at a right
vertex `v` whose left endpoint has full label `g`. For each previously
assigned right vertex `w`, right-label agreement contributes the
candidate-dependent term

\[
 q'(v,w)=\sum_g h_v(g)h_w(g).
\]

Thus the right pass minimizes `sum(scores[previous_right_label])` with
`shared=\sum_g h_v(g)h_w(g)`, exactly as in the source. Again all
unassigned labels cost zero and the two tie-breaks preserve minima.

**Conclusion 1:** Each vertex assignment weakly decreases the conditional
expectation of `F`. The fully labeled graph therefore satisfies

\[
 F_\mathrm{final}\le\mathbb E F_\mathrm{uniform}\le 2M\Delta.
\]

For the last inequality, disjoint-endpoint edge pairs contribute zero
to the covariance expression for `E[F]`. At most `2M Delta` ordered
pairs share an endpoint, and each contributes at most one.

A stronger, exact integer check uses the number of ordered edge pairs
sharing left endpoints `S_l`, right endpoints `S_r`, and **both**
endpoints `B`:

\[
 D\mathbb E F_\mathrm{uniform}
 = (R-1)^2 B+(R-1)(S_l+S_r).
\]

The independently implemented oracle
`reference/packing_proof.py::conditional_objective_numerator` calculates
conditional expectations from edge pairs directly, not from the sparse
scores. Checkpoint tests verify **each** production choice is a minimizer,
including repeated endpoints, empty-degree vertices, and ties.

## 2. From collision load to packet count

Write `X_max` for the largest full pair-label class. From nonnegativity
of the summands in `F`:

\[
 X_\max\le M/D+\sqrt{2M\Delta}.
\]

Set `Hpad=L*ceil(X_max/L)`, exactly the computation in `pack`. Under the
paper's three **numerical** requirements

\[
 M\ge 2D^2\Delta,\quad M\ge LD,\quad 2L\le\Delta,
\]

we have `sqrt(2M Delta) <= M/D` and `L <= M/D`, hence

\[
 H_\mathrm{pad}\le M/D+\sqrt{2M\Delta}+L\le 3M/D.
\]

For every coordinate, normalize an ordered pair of endpoint symbols to
an unordered pair. A family with `a'` unequal coordinate pairs
contains exactly `2**a'` full ordered pair labels. In that family each
packet uses `2**(a-a')` slots per ordered label, so the number of
potential packets is `Hpad*2**a'/L`. The sum of `2**a'` across all
families is

\[
 \bigl(r+2\binom{r}{2}\bigr)^a=r^{2a}=D.
\]

Consequently the full padded construction uses at most `Hpad*D/L <=
3M/L` packets. The **implementation discards wholly empty families and
wholly empty packets**, which can only reduce this count, never omit a
real edge. `pack` verifies that the sorted real slot identifiers equal
`range(M)`; tests also check the slot orientations.

Each fixed coordinate and fixed symbol occurs on either side in exactly
`D/r` full pair labels. Padding each label class to `Hpad` slots gives
at most `Hpad*D/r <= 3M/r` real ports of that symbol on either side.
The implementation's omission of empty slots never increases that load.
For a packet family, slot bit `i` either selects one of the two
orientations (unequal symbols) or distinguishes copies (equal symbols),
so every real edge occupies the same original slot at both endpoints
and meets the packet-orientation rule.

**Conclusion 2:** For valid bipartite incidence and the lemma's
numerical hypotheses, `balanced_labels` followed by `pack` satisfies
the packet-count, per-coordinate real-port load, orientation, and
conservation statements of the packing lemma.

## 3. Reproducible implementation witnesses

Run:

```bash
PYTHONPATH=src:. python -m pytest -q tests/unit/test_packing_conditional_expectation.py
PYTHONPATH=src:. python scripts/packing_proof_audit.py --output packing-proof.json
```

The first command runs an **independent** conditional-expectation oracle
on small multigraphs and checks every left/right greedy decision. The
second constructs degree-regular, degree-bounded bipartite graphs that
meet the *actual inequalities*, including two-coordinate packets and
parallel edges. Its JSON reports `D*E[F]`, `D*F_final`, numerical
hypotheses, padded class maximum, packet count, and side loads. The
individual finite witnesses do not replace the general argument above.

## 4. What is not established here

- These numerical conditions do not hold for the earlier finite
  `r=64,a=2` Sudoku probes, so their packet-count failures remain
  outside the theorem's hypothesis regime.
- The paper's literal active schedule requires exceptionally large
  inputs. The default bounded leaf, modes, memory and time policies
  still admit capacity refusals on ordinary Sudoku boards.
- This lemma does not prove recursive packet-oracle bit costs,
  coefficient precision and recovery bounds, or worst-case total
  running time. It also does not turn a bound in Boolean network edges
  into a `2**o(N)` claim in Sudoku cells.

The packing obligation is distinct from those remaining theorem-interface
and complexity questions.
