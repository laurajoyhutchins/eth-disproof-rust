# Exact projected Gram elimination: bit work, minors, and storage

**Scope:** the actual \`_projected_group_rows\` stage of
\`src/non_exponential_sudoku/eth/construction.py\` when the auxiliary is
\`ImplicitAuxiliaryDesign(measurement_basis="projector")\`. Its production
implementation now calls
\`src/non_exponential_sudoku/eth/projected_gram.py\`.

This is a **source-correspondent, explicit polynomial bit-machine
upper bound for the projected Gram and basis-reduction stage**, including
individual projector entry requests, integer row reduction,
normalization, and their retained coefficient storage. This is NOT
a worst-case complexity theorem for the entire ETH/Sudoku pipeline.

## 1. Scale the actual projector restriction to integers

Fix one occupied coordinate-label copy and one variable group of
size \(g\). Let \(L_v\) be the occupied auxiliary labels assigned
to an active variable \(v\) in this copy. These label sets partition
a subset of the \(\ell\) input occurrences, so
\(\sum_v|L_v|=L\le\ell\).
Let \(k\le\min(g,L)\) be the number of active variables.

The source constructs the restricted exceptional Gram matrix

\[
G_{v,w}=\sum_{a\in L_v}\sum_{b\in L_w}P_{a,b},
\]

where \(P\) is the exceptional spectral projector. The source
implementation of \`exceptional_projector_at\` has denominator
\(2^{s+t}\), where \(s+t\le Q\), and its numerator is an integer.
Therefore

\[
A:=2^QG\in\mathbb Z^{k\times k}
\]

**without** constructing the virtual \(D=r^{2Q}\) matrix,
selector rows, or arbitrary rational common denominators.

Each projector entry has absolute value at most 1 because it is an
entry of an orthogonal projection. This can also be checked directly
from the binomial coefficient formulas. Consequently

\[
 |A_{v,w}|\le 2^Q\,|L_v||L_w|
      \le 2^Q L^2.
\]

A deliberately slack, integer-valued input ceiling is

\[
 B=Q+4+2\lceil\log_2(L+1)\rceil.
\]

All Gram entries therefore have at most \(B\) bits. The
implementation checks this exact inequality for every real
constructed entry.

## 2. Replace rational RREF by a fraction-free determinantal algorithm

For \(A\in\mathbb Z^{k\times k}\), use fraction-free
Gauss-Jordan/Montante reduction. After selecting a nonzero pivot
\(p=A_{r,c}\) and remembering the previous pivot \(p_{\rm old}\),
each off-pivot entry is updated by

\[
 A'_{i,j}=
 \frac{pA_{i,j}-A_{i,c}A_{r,j}}{p_{\rm old}}
 \qquad (i\ne r,\ j\ne c).
\]

Zero columns are skipped. Row swaps are allowed. By the
Sylvester determinantal identity, each division is exact and
every stored intermediate is a signed minor of the original
integer matrix. The implementation explicitly checks every
remainder and rejects a violated minor-size invariant.

Leibniz's determinant bound gives
\(|\det A_{I,J}|\le k!\,(2^B)^k\). Thus all stored intermediate
integers, as well as primitive normalized basis entries, have
at most

\[
 \boxed{B_{\rm minor}=
       k(B+\lceil\log_2(k+1)\rceil)+4}
\]

bits. The transient integer multiplications/subtractions have
at most \(2B_{\rm minor}+4\) bits.

After elimination, normalize each nonzero pivot row by the
**integer gcd** of its entries, then orient it so its pivot is
positive. This gives exactly the primitive integral rows returned
by the former \`Fraction\`-RREF with lcm/gcd normalization. Because
this procedure only uses integral arithmetic, rational intermediate
denominators no longer accumulate independently.

This is an exact **representation-preserving** change, not a
new rank assumption. Matrix rank can still be as large as \(k\),
and the number of transferred rows remains subject to the
independent measurement admission conditions.

## 3. Explicit bit work and retained bit-cell envelopes

\`projected_gram_envelope\` computes unconditional, allocation-free,
integer ceilings for a single call from \((g,L,k,r,Q,R)\).
The stage makes at most \(L^2\) distinct projector queries.
Each source query scans \(O(Q)\) label entries and sums at most
\(O(RQ)\) products of binomial coefficients of bit length \(O(Q)\).
The Gram matrix contains \(k^2\) entries. The Montante sweep has
at most \(O(k^3)\) integer pivot updates and exact divisions, with
operands bounded above by \(2B_{\rm minor}+4\) bits. Primitive row
normalization adds \(O(k^2)\) Euclidean GCDs on integers with at
most \(B_{\rm minor}\) bits.

A concrete conservative reference-machine work ceiling, including
the projector-oracle and label-index work, is encoded as

\[
\begin{split}
T_{\rm Gram}\le 2^{20}\Bigl[&
(L+1)^2(Q+1)^5(R+1)(I+B_t+1)^3\\
&+(k+1)^4(B_{\rm minor}+1)^4\\
&+(g+L+1)^4(B_t+1)^2
\Bigr],
\end{split}
\]

where \(I=Q(\lceil\log_2(r+1)\rceil+2)+4\) bounds
label-index storage, and \(B_t=2B_{\rm minor}+4\)
bounds transient integer values. Every term is polynomial in
the **numeric source parameters and their bit widths**.
The constants supply headroom for schoolbook multiplication,
long division, binary indexing, Euclid, sorting/copying metadata,
and table operations of this specifically described reference machine.
This bound is not a count of CPython VM instructions or native
\`math.comb\` internal machine operations.

The corresponding explicit \`retained_abstract_bit_cells_upper\`
accounts for up to \(L^2\) cached projector query results and label
references, \(k^2\) integer matrix entries, scratch,
\(k g\) primitive basis integers, and schedule-index metadata.
It is also polynomial and independent of \(D\).
The implementation separately records actual integer operands,
counts of adds/multiplies/exact divisions/Euclidean divisions,
peak observed integer widths, matrix entries, and projector-cache size.
It asserts observed modeled **integer** bit steps do not exceed
its symbolic ceiling. The recorded per-operation bit-step sum is
not confused with native interpreter instructions.

## 4. Compose across the whole projected-transfer stage

The production source invokes the projected Gram reducer once
per interpolation center, group, and occupied label copy.
There are \(Q\) centers, \(r\) groups, and no more than
\(\ell\) nonempty copies. Under the *source's already checked*
balancing inequality \(r|S_g|\le2n\),

\[
\begin{aligned}
  k&\le\min(\lceil 2n/r\rceil,\ell),\\
  \#\text{Gram calls}&\le Qr\ell.
\end{aligned}
\]

\`projected_transfer_gram_envelope(n,ell,r,Q,R)\` calculates the
product of that count and the worst per-call bit-work ceiling.
Its simultaneous bit-storage ceiling includes scratch space for
one live Gram reduction **plus all retained primitive measurement
rows from earlier groups/copies/centers**.

For the manuscript's conditional parameters
\(Q=O(\log n)\), \(r=O(\sqrt{\log n})\),
\(R=O(\sqrt{\log n})\), and bounded-occurrence input
\(\ell\le3n\), these are **polynomial-in-\(n\)**
bit-work and bit-storage bounds for the *projected Gram stage*.
The numeric parameter inequalities must hold independently;
a toy finite instance passing these tests does not satisfy the
paper's entire admission.

The transfer envelope assumes the source's group-size inequality,
not that \`choose_balanced_schedules\` has been proved total for
every admitted CNF. It also excludes input CNF normalization,
all replacement-row generation, balancing, row-space certificate
verification, full interpolation, and the recursive contraction
routine. The strict manuscript entrypoint still defaults to
**selector** measurements, not this projected mode, and may refuse
under practical resource caps.

## 5. Verification and remaining theorem gap

The tests compare hundreds of randomized, rank-deficient and
full-rank integer matrices against an independently implemented
rational Gaussian RREF. They compare real implicit projector Gram
bases with the previous production rational implementation,
including zero-rank and sparse occupancy cases. Existing
end-to-end implicit-source transfer/certification tests and
actual full deformation oracle tests run unchanged.
A huge virtual-\(D\) projector group is queried without
materializing the auxiliary matrix, and a symbolic all-center
envelope is calculated without enumerating variables or labels.

Reproduce:

\`\`\`bash
PYTHONPATH=src:. python -m pytest -q tests/eth/test_projected_gram.py tests/eth/test_implicit_auxiliary.py tests/eth/test_implicit_height.py
python -m mypy --strict --no-incremental
\`\`\`

**Claim boundary:** This settles the projected *Gram/RREF stage*
under its explicitly stated source and bit-machine model. It does
not establish non-refusal of the strict paper entrypoint, prove
the number/bit size of all recursion intermediates is subexponential,
or imply a non-exponential worst-case #SAT/Sudoku algorithm.
The complete theorem gate remains **RED**.



**Executed verification:** GitHub Actions
[run 42723444144](https://github.com/laurajoyhutchins/nonexp-sudoku/actions/runs/42723444144)
passed strict production mypy across **81 source files**, plus
**63 exact tests**, with **one optional FLINT test skipped**
because \`python-flint\` was not installed on that runner.
The test set included the randomized rational-RREF differential,
real high-dimensional implicit projector, source Gram/transfer,
balancing, spectral-factor-width, origin-readout and spectral-rank
regressions. A prior isolated targeted run
[42723276527](https://github.com/laurajoyhutchins/nonexp-sudoku/actions/runs/42723276527)
also passed 32 tests and strict typing.

The source change is limited to the projector-mode Gram branch.
Original selector-mode computation and its numerical admission
checks were not replaced or reinterpreted.
