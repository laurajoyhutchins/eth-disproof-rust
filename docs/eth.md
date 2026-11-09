# Exact CNF, reductions, and interpolation

`CNFFormula` retains **declared variables**. For an empty conjunction on `m`
variables there are `2^m` assignments, whereas an empty clause gives zero.
Eliminating free variables therefore requires an explicit multiplicative
power-of-two factor. Tseitin-style helper variables require a *unique*
extension to be parsimonious, not just equisatisfiable.

The bounded CNF preprocessing and disjoint-leaf sparsification implementations
state their counting identities and enforce finite resource limits. Their
small-instance reference is deliberately exponential brute-force enumeration;
Ganak is an independent optional oracle, not the implementation of the
proposed general algorithm.

The construction modules build rational-polynomial measurements and perform
exact Taylor/Hermite recovery. The exact coefficient arithmetic and separated
measurement checks are tested independently from the candidate parameter
admission. Constructing a small exact instance does not prove that a full
worst-case recurrence achieves the paper's asymptotic bound.

See `eth/{cnf,preprocess,sparsification,polynomial,design,taylor,interpolation,
construction,parameters}.py` and their checkpoint tests. The goal is to make
incorrect count preservation, inaccurate interpolation or unbounded
intermediate work **falsifiable**, rather than hide it behind a single solver
entrypoint.

## Exact arithmetic representations

The `Polynomial` and `Jet` classes are canonical, independent `Fraction`
reference implementations. They never require FLINT. The optional FLINT
backend retains `fmpq_poly` objects throughout the Boolean-cube deformation
reference calculation and the incremental Hermite reconstruction. The
restricted Taylor evaluator retains native truncated jets in the same way.

Input coefficients cross into FLINT once per use, and full coefficients are
exported to validated `Fraction` values only at public result boundaries.
Export constructs fractions directly from integer numerators and denominators;
there is no string conversion or floating-point intermediary. Native
numerators and denominators are inspected at the same coefficient-bit
checkpoints as the reference implementation. The operation ledger charges
logical schoolbook work under **both** backends; its counts must not be
interpreted as elapsed native instructions or a complexity improvement.

Hermite uses a local, explicit truncation order on `fmpq_poly`, not FLINT's
process-global series cap. Differential tests check exact results, refusal
conditions, operation statistics, and the number of public exports. Ganak
remains a separate, independent #SAT correctness oracle.


## Exact coefficient-compression experiments

The auxiliary spectral polynomial for alternating values on consecutive
integers uses the integer-valued Newton basis

`f(W) = (-1)^a sum_{j=0}^{R-1} (-2)^j * binom(W-a,j)`.

Its Walsh/Fourier coefficient depends only on the cardinality of its
subset, and vanishes above degree `R-1`. The cardinality transform in
`eth/construction.py` replaces the original `4**Q` coefficient
enumeration. **It does not remove the dense `D = r**(2*Q)` auxiliary
rows**: that remains a separate practical obstacle.

For a general rational Hermite polynomial of degree less than the number
of Taylor conditions, `interpolate_origin_hermite` reads the value at zero
using a local CRT functional, without constructing the full polynomial.
The routine does not certify an independent tighter degree claim for
inconsistent overdetermined data. The constructed #SAT path uses it only
after validating its replacement system and certifying the Taylor
measurements. `count_from_constructed(..., readout='polynomial')`
retains the full original rational reference for differential comparison.

`eth/modular_readout.py` provides a separate exact finite-ring origin
functional. Rational inputs are accepted only if their denominators and
Hermite center differences are invertible modulo the selected moduli.
The bounded CRT readout requires a **proved bound on the true integer
origin** before reconstruction. This applies to count-valued deformations,
not automatically to the revised paper's parity-lift scalar whose value
is only congruent to the count modulo a power of two. The modular
prototype receives *precomputed rational Taylor jets*, so it does not
yet prevent upstream rational coefficient growth.

The paper's parity-lift linear coefficients have the closed form
`e_0(Y)=1-Y` and `e_j(Y)=(-1)^j binom(2*j,j)/2 * (1-2Y)` for `j>=1`.
They have linear bit height in `ell`; the helper and independent
polynomial-identity tests are in `eth/parity_lift.py`. The general
parity-lift counting path itself is not yet implemented.

Reproduce isolated algebraic experiments and a tiny end-to-end
constructed-count comparison (not a worst-case scaling claim):

```bash
PYTHONPATH=src:. python -m benchmarks.eth.algebraic_readout --repeats 3 --output readout.json
```

## Implicit auxiliary operator and measured evidence

`construct_implicit_auxiliary(r,Q,R)` is the default for
`construct_bounded_designs(...)`. The original `construct_auxiliary`
remains a separately executable dense correctness oracle, and
`construct_bounded_designs(..., representation='dense')` selects it
explicitly. Both use identical spectral interpolation and measurements.

The new `ImplicitAuxiliaryDesign` represents `f(W)` by an exact
`(Q+1) x (Q+1)` kernel indexed by the number of diagonal coordinates
and unswapped off-diagonal coordinates. Individual `P[u,w](T)`
coefficients are calculated when needed. Exceptional product
eigenvectors are stored as selector tuples, never vectors of length
`D=r**(2*Q)`. Transfer now iterates only over occupied incidence
labels, rather than constructing all `D` labels or all `D**2` row
entries. The implementation counts exceptional selectors
combinatorially before allocation and refuses if the bound is exceeded.
It also has an explicit maximum for `Q` in this research backend.

**Observed on GitHub-hosted Python 3.13, 2026-11-09, workflow run
`42669627090`:**

| r | Q | R | dense seconds | implicit seconds | dense peak traced bytes | implicit peak traced bytes |
|---|---|---|---|---|---|---|
| 2 | 2 | 2 | 0.00872 | 0.000603 | 27,312 | 4,222 |
| 2 | 3 | 2 | 0.04497 | 0.000847 | 168,352 | 3,936 |

The Q=12,R=12 implicit constructor completed in 0.00656 seconds with
20,312 peak traced Python allocation bytes. Its virtual `D` was
16,777,216, corresponding to 281,474,976,710,656 potential dense
matrix entries, but only 169 kernel coefficients and one exceptional
selector were retained. No dense Q=12 timing was attempted.

**End-to-end witness on the same GitHub-hosted setup, workflow run
`42669890039`:** for a *three-variable* CNF and implicit
`r=2,R=Q`, `Q=5` and `Q=12` each produced exact count 4,
matching independent exhaustive enumeration. Counting took about
0.51 seconds and 1.29 seconds respectively (under Python
`tracemalloc`; timings include its overhead). The completed operator
preparation took about 0.002 and 0.013 seconds. This establishes that
a huge *virtual* dimension does not require allocating the dense
matrix; it is not evidence for improved worst-case scaling in the
number of Boolean variables. Only the `R=Q` spectral regime was
exercised at the huge dimension, where the exceptional-direction count
is one. General regimes can retain exponentially many exceptional
directions and are explicitly resource-limited.

Reproduce these measurements with
`PYTHONPATH=src:. python -m benchmarks.eth.implicit_auxiliary_probe`;
and exercise the larger count as an optional integration test:
`python -m pytest -q tests/integration/test_implicit_large_dimension.py`.
The one-off GitHub benchmark workflow was removed after the measurements
to avoid a permanent extra CI job.


## Restricted exceptional projectors instead of global eigenvectors

The optional `measurement_basis='projector'` mode of
`construct_implicit_auxiliary` does not enumerate any of the
`C = sum_{j outside interval} binom(Q,j)
(r(r-1)/2)^j (r(r+1)/2)^(Q-j)` exceptional tensor eigenvectors.
Its `exceptional_count` remains exact metadata, even when C is enormous.

For two auxiliary labels u,v, each diagonal local coordinate contributes
1 to the projector generating function; an identical off-diagonal pair
contributes `(1+z)/2`, and a swapped off-diagonal pair `(1-z)/2`.
Incompatible pairs contribute 0. Sum coefficients of z^j outside the
spectral interval to obtain the exact entry of the **orthogonal** projector
onto the exceptional space. This is independently compared against the
orthogonalized *original tensor eigenvectors* in the checkpoint tests.

If B is the original exceptional measurement basis and A maps occupied
labels to a group's variables, the restricted Gram matrix

`G = A^T P_exceptional A = (B_orthonormal A)^T (B_orthonormal A)`

has exactly the same **rowspace** as all original measurements restricted
to those occupied coordinates. An exact rational RREF of G supplies
independent integral rows. This is essential: raw primitive Gram rows may
have huge integer coefficients, increasing the Taylor range
`(2D+1)^measurements`; full-rank RREF instead yields unit-coordinate
rows with `D=1`. All transferred center certificates are still independently
verified, and `max_measurement_rows` applies to the **actual retained**
rows, not the unenumerated global eigenspace size.

**Measured evidence:** GitHub-hosted CPython 3.13, 2026-11-09,
workflow `42674871268` (one-off workflow removed after capture):

| r | Q | R | Global exceptional basis size | Retained selectors | Certified rows | Maximum row L1 | Exact count | Count seconds |
|---|---|---|---:|---:|---:|---:|---:|---:|
| 2 | 2 | 2 | 1 | 0 | 1 | 1 | 4 | 0.012 |
| 2 | 12 | 2 | 8,549,722 | 0 | 3 | 1 | 4 | 0.061 |
| 2 | 48 | 8 | 14,603,500,803,275,681,828,904,645,562 | 0 | 3 | 1 | 4 | 0.216 |

At Q=48,R=8, auxiliary preparation was 0.195 seconds with
152,384 peak traced bytes and transferring/certifying all 48 centers
took 0.376 seconds with 187,408 peak traced bytes. The virtual
D=4**48 and virtual matrix size D**2 are never allocated. The
complete three-variable count was independently checked against
exhaustive enumeration and preserved as an optional integration test.

These results **do not establish the paper's measurement bound**
`tau <= 1/(r*lambda)`: the rank of a restricted exceptional
projector can equal the entire observed variable space. For a
large real CNF, that can leave too many measurements even though
the global eigenvectors are never enumerated. The example has
three Boolean variables, so increasing Q is not evidence of
subexponential scaling in the input size.

Reproduce with
`PYTHONPATH=src:. python -m benchmarks.eth.projector_probe`.
The original `measurement_basis='selectors'` remains the default
for exact differential comparison; selecting a dense representation
with projected measurements is deliberately rejected.


### Finite-size measurement rank obstruction

An independent one-off GitHub run `42675396786` computed the **exact
restricted projector rank**, without performing a full CNF count, for
disjoint two-literal clauses and deterministic incidence schedules at
fixed `r=2,Q=12,R=2`:

| Declared variables | Minimum / maximum center rank | Maximum row L1 | Observed tau | Illustrative 1/(r*ceil(log2(n))) |
|---:|---:|---:|---:|---:|
| 4 | 4 / 4 | 1 | 1/2 | 1/4 |
| 8 | 8 / 8 | 1 | 1/2 | 1/6 |
| 16 | 16 / 16 | 1 | 1/2 | 1/8 |
| 24 | 24 / 24 | 1 | 1/2 | 1/10 |

The rowspace has full observed rank. **No exact change of measurement
basis can lower its row count for these instances.** RREF reaches the
minimum and unit vectors reach the minimum L1 norm, but the Taylor
measurement-value loop retains `(2*D+1)^rank=3^n` work in this
configuration. The paper's literal `n`-derived parameters are NOT
admitted for these tiny formulas; the target column illustrates the
shape of its `tau` bound, not an applicable theorem instance.

The next mathematical bottleneck is therefore either a different
low-rank construction with independently certified separation and
the paper's quantitative rank limit, or an exact method to evaluate
measurement-value sums without enumerating every value tuple.
Merely encoding the projector more succinctly cannot reduce rank.
The rank sweep is reproducible via
`PYTHONPATH=src:. python -c "from benchmarks.eth.projector_probe import rank_audit; print(rank_audit())"`.


## Sparse multilinear Boolean-polynomial contraction (opt-in)

A dense *variable-scoped* factor table need not imply a dense Boolean
polynomial. The exact deformed clause expression
`1 - product_l false_l(sum_v P[e,l,v](T) x_v)` has multilinear degree no
greater than the number of literals in its clause, regardless of the
number of nonzero `P[e,l,v]` coefficients. In the Boolean quotient
ring, `x_v**2=x_v`, so products of monomials are keyed by the **union
of their variable sets**, not by polynomial exponent tuples.

The optional `summation='multilinear'` mode stores an exact sparse
dictionary from Boolean variable-subset bitmasks to rational truncated
Taylor jets. It multiplies clause polynomials in this quotient ring, and
evaluates the sum over all Boolean assignments by the linear identity

```
sum_{x in {0,1}^n} x^S = 2**(n - |S|)
```

for every monomial `S`. This is *not* exhaustive assignment iteration.
The Taylor pair counter and factor-table assignment counter remain zero.
Separate counters record the exact number of **attempted multilinear
term products** and maximum retained **nonzero Boolean monomials**.

A *single* width-two clause with replacement coefficients involving
all `n` variables has at most `1+n+binom(n,2)` distinct Boolean
monomials, compared with `2**n` possible rows in its full variable
factor table. The TDD witness constructs this case at n=16 and verifies
the exact count. For multiple clauses, however, multiplication can
produce all `2**n` monomials, and the test suite deliberately requires
a capacity refusal on such a family. Neither small clause width nor a
small jet truncation order alone bounds the total retained support.

The `max_factor_entries` budget limits sparse monomials,
`max_factor_total_entries` bounds simultaneously retained input/output
dictionary entries during multiplication, and `max_factor_work` bounds
attempted **term products**. These are entry-count limits, **not**
byte-accurate process RSS bounds. The existing exact-jet operation,
coefficient-bit and degree limits still apply.
A refusal is never interpreted as a zero count. The representation
does not prove any subexponential bound: the cost of manipulating
n-bit monomial masks and exact rational coefficient operands must be
accounted for, and the polynomial product may have exponential support.

This is a fourth, independent finite-instance evaluator alongside
`tuples`, group-factor `eliminate`, and Boolean-table `fused`.
The original methods remain unchanged and the default is still
`tuples`. Because the monomial method does not build factor tables,
its `factor_scope_basis` is `not_applicable`; compare its
`multilinear_support_peak`, not the unrelated group/variable
scope-width fields. Full-pipeline use still goes through the certified
construction, Hermite reconstruction, and count-preserving reductions,
allowing direct comparison with the ETH reference algorithm.

```bash
python -m pytest -q -m integration tests/eth/test_sparse_multilinear.py
python -m scripts.eth_reference --summation multilinear
```

## Boolean-difference fusion into exact polynomial factor elimination (opt-in)

The original separated Taylor evaluator explicitly sums all pairs
`U subset E subset [n]` with `|E|<=q`, which requires

`sum_{j=0}^{min(q,n)} binom(n,j)*2**j`

restricted contractions **per center**. This is the source of the
Taylor-pair explosion measured by the full CNF benchmark.

There is an exact algebraic reorganization. For a fixed Boolean assignment
`x`, each restricted term replaces the original evaluation at `t` by
`P_e,v(t) * x_v + (P_e,v(t+z)-P_e,v(t)) * 1_{v in U}`,
with `E` forced active in `x`. The alternating `U`-sum is the
multivariate Boolean finite difference on `E`. It annihilates all
products involving fewer than `|E|` of the increments; each increment
is divisible by `z`. Hence terms `|E|>q` vanish modulo `z**(q+1)`.
Summing the **entire** Boolean finite difference first telescopes to the
single polynomial factor contraction

```
[z**<=q] sum_{x in {0,1}^n} prod_{clauses e}
    (1 - prod_{literal ell in e} false_ell(
        sum_v P[e,ell,v](t+z) * x[v]))
```

where `false_ell(a) = 1-a` for positive literals and `a` for negative
literals. This identity retains the *same* certified deformed polynomial
and the exact same Taylor coefficients, but never explicitly materializes
the `(E,U)` expansion.

`summation='fused'` is an **opt-in** third evaluator that applies exact
variable elimination to clause factors with scopes determined by the
nonzero *truncated polynomial coefficients*. It retains the original
independent measurement certificate and checks exact bit and resource
limits. `taylor_pairs=0` now means the explicit pair loop did not run.
Factor assignments, maximum table entries, and induced factor scope
still record the real work. The scope basis is **Boolean variables of
the prepared CNF leaf**, including any count-preserving reduction auxiliary
variables, unlike the `summation='eliminate'` group-mask evaluator.
The two kinds of scope counts are **not** comparable without translation.

This is classical factor elimination applied to a polynomial deformation.
Its worst-case width can still be `n`. A measurement certificate with
few rows does **not** guarantee sparse polynomial coefficient supports;
spectral mixing may make them dense. The fused backend is therefore an
independent test of whether finite-difference materialization was the
dominant bottleneck, **not** a proof of subexponential #SAT or of the
paper's quantitative admission. The separated tuple and group-factor
implementations remain available and the default remains `tuples`.

The integration tests compare every Taylor coefficient at multiple
nonzero centers and truncation orders against the original evaluator,
check completed end-to-end counts against an independent Boolean oracle,
and require fail-closed capacity refusal on oversized fused factor tables.

Reproduce selectively:

```bash
python -m pytest -q -m integration tests/eth/test_fused_taylor.py
python -m scripts.eth_reference --summation fused
```

## Exact Taylor group-factor elimination (opt-in)

`taylor_coefficients_separated(..., summation='eliminate')` and
`restricted_taylor_sum(..., summation='eliminate')` use the exact
`eth/factorized_taylor.py` bucket-elimination implementation. The same
switch is available on both certified Hermite count functions and
`count_from_constructed`. `summation='tuples'` remains the original
reference and the default until a general performance cutover is proven.

Mathematically, every local Boolean mask `x_g` determines exactly one
measurement signature `y_g=M_g x_g`. Therefore

`sum_y prod_g sum_{x_g:M_g x_g=y_g} F_g(x_g,y)`

equals a direct sum over group assignments, with each clause represented
by a factor on its owner group and only those foreign groups for which
the **independently certified** measurement coefficient is nonzero.
Exact bucket elimination contracts these factors using truncated rational
or FLINT jets, without visiting all measurement-value tuples. It does
NOT weaken the certificate or invoke brute-force counting as a fallback.

The relevant complexity is induced factor scope: its Boolean mask
domain product, factor table size, and total exact arithmetic work.
These are explicitly bounded by `TaylorLimits.max_factor_entries`,
`max_factor_total_entries`, `max_factor_work`, and the existing
`max_jet_operations` / `max_coefficient_bits`. Statistics record
`factor_scope_peak`, `factor_entries_peak`,
`factor_assignments_tested` and `factor_eliminations`. The
`measurement_tuples` statistic is zero in this mode; it is a **work
counter**, not a claim that the mathematical measurement space is empty.

**Measured** on GitHub-hosted Python 3.13, November 9, 2026,
workflow `42677326298`. Each formula is a path of binary positive
clauses connecting the first variable of adjacent two-variable
groups. Its independent count oracle is `F_(n/2+2) * 2^(n/2)`.

| n | Old measurement tuple space | Factor assignments tested | Max factor entries | Count-only seconds |
|---:|---:|---:|---:|---:|
| 4 | 81 | 36 | 12 | 0.020 |
| 8 | 6,561 | 100 | 12 | 0.038 |
| 12 | 531,441 | 164 | 12 | 0.072 |
| 20 | 3,486,784,401 | 292 | 12 | 0.171 |
| 32 | 1,853,020,188,851,841 | 484 | 12 | 0.378 |
| 64 | 3,433,683,820,292,512,484,657,849,089,281 | 996 | 12 | 1.338 |

The original tuple evaluator was **measured** at n=4 (0.038 s)
and n=8 (4.272 s, versus 0.038 s for elimination). Larger old-column
values are exact theoretical iteration counts, not runtime
measurements. Under `tracemalloc`, peak traced allocations in the
64-variable calculation were 1,083,664 bytes. The exact count was
24,493,713,157,783,552. The maximum induced scope was 2 groups,
and all counts are reproduced by the benchmark.

Run `PYTHONPATH=src:. python -m benchmarks.eth.factorized_taylor_probe`.

**No general ETH claim:** This is ordinary exact variable elimination
on the certified *group interaction graph*. A group clique or a family
whose induced width grows with n retains exponential tables or fails
closed on the explicit budget. The chain example demonstrates an
implementable structural regime rather than a solution for arbitrary
worst-case CNF, and does not satisfy the manuscript's huge literal
n-derived parameter schedule.


**Independent integration verification:** one-off GitHub run
`42677879381` installed `python-flint` and passed all five
`tests/integration/test_implicit_large_dimension.py` cases,
including the 64-variable factorized chain, plus the explicit
FLINT-vs-Python exact-jet equality check (one passed). The
`factorized_taylor.py` engine uses the same checked jet arithmetic
on both backends. This is mathematical equivalence evidence on
the tested fixtures, not a benchmark establishing which arithmetic
backend is faster in this new contraction regime.


## Measurement count does not certify low group-factor width

The exact certified factor scopes are a distinct property from the rank and
number of measurement rows. `audit_factor_width(certificate)` derives one
scope per clause, consisting of the owning group and precisely those foreign
groups with nonzero *certified* lambda coefficients. It constructs the
undirected primal group graph, simulates the same min-domain elimination
ordering as `factorized_taylor.py` on those scopes, and records the maximum
induced scope size and the base-2 exponent of the maximum possible dense
table domain. It allocates no Boolean-mask tables.

**Counterexample family:** Let r>=3 groups each contain s variables.
For every unordered pair {g,h}, give group g a distinct boundary
variable x_(g,h), group h another x_(h,g), and add
`(x_(g,h) OR x_(h,g))` with owner g. Within each group, use a
directed cyclic series of 2-literal implications among its r-1
boundary variables; together they force those variables equal.
Every boundary variable appears in exactly three clauses: one
cross-group clause and two implications. Pad each group to size s
using independent local two/three-literal disjunctions, with all
variables active and no width/occurrence violations.

Use the identity replacement polynomial (degree zero) and one unit
coordinate measurement row for *each* boundary variable in its
group. The total number of measurement rows is r(r-1), each of L1
norm D=1, and the groups are perfectly balanced. With n=r*s,

`tau = r(r-1)/(2*n) = (r-1)/(2*s)`.

Thus for arbitrarily large r, choosing s sufficiently large can meet
the *numerical* target
`tau <= 1/(r*ceil(log2(n)))` while all pairwise factor scopes
produce the complete group graph K_r. Its structural treewidth
is exactly r-1, independent of elimination order. The small
measurement bound by itself cannot imply a low-width factorization.

**Executed evidence:** GitHub Actions run `42680799964`
(2026-11-09), CPython 3.13, independent `certify_measurements`
against the identity replacement, with real CNF normalization:

| r | n | Clauses | Literal incidences | Measurement rows | D | tau | Illustrative target tau | Exact treewidth |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 66 | 39 | 78 | 6 | 1 | 1/22 | 1/21 | 2 |
| 4 | 192 | 106 | 216 | 12 | 1 | 1/32 | 1/32 | 3 |

The maximum literal occurrence was three and clause width was
at most three. The largest *possible dense domain* in the min-domain
group elimination had respectively 2**66 and 2**192 Boolean
assignments, but these numbers are **not measured work or hardness
lower bounds**. For the unpadded r=3 and r=4 versions, exact #SAT
is r+1, independently checked by exhaustive enumeration and by the
factorized Taylor evaluator. The padded instances are also
easy by analytic reasoning (vertex covers of K_r times local
independent disjunction counts). A better algorithm can exploit
their equality and local factorization structure.

**Claim boundary:** These are valid manually certified separated
designs at arbitrary nonzero centers with identical degree-zero
replacements. They do **not** come from the paper's prescribed
n-dependent r,Q,R auxiliary construction; satisfying the numerical
tau inequality does not satisfy the paper's full admission. This
falsifies only the inference *measurement count => low group
interaction width*. It neither contradicts a proof about the
specific paper construction nor proves an exponential time lower
bound for #SAT.

Reproduce using
`PYTHONPATH=src:. python -m benchmarks.eth.factor_width_obstruction`.
The research generator and its small exact oracle live in
`benchmarks/eth/factor_width_obstruction.py` and
`tests/eth/test_factor_width_obstruction.py`.

## Bounded end-to-end executable path

`count_cnf_reference(formula, config=ReferencePipelineConfig(...))` now
connects the previously isolated exact operations:

1. If the input exceeds the sparsifier's clause-width `k`, first apply
   count-preserving width/occurrence reduction while recording the
   removed-free-variable multiplier.
2. Enumerate the **disjoint** sparsification leaves, stopping with an explicit
   capacity refusal if the complete tree exceeds its configured budget.
3. For **every** leaf, re-project free variables and apply parsimonious
   width/occurrence reduction, since branching can add occurrences.
4. With at least two active variables, construct and certify auxiliary
   measurement designs, evaluate separated Taylor coefficients, and
   reconstruct the exact count by Hermite interpolation. Never substitute
   brute-force or Ganak on a failure.
5. For zero or one active variables, use the explicitly reported 1- or
   2-assignment base case. Restore all leaf multipliers, sum only after
   successful leaf evaluation, then restore the initial multiplier.

The return type contains a complete count and per-leaf evidence: branch path,
preprocessed dimensions, restored contribution, execution method, center
count, Taylor pair count, measurement tuples, peak factor scope and entries,
total factor assignments and eliminations, and coefficient-size observations.
Factor work is reported for each constructed leaf and is zero for the explicit
0/1-variable base case. Peaks are per-center maxima; work is summed over
centers. In particular, `measurement_tuples=0` with `summation='eliminate'`
means the tuple evaluator was bypassed, **not** that exact counting was free.
The factor counters measure algorithmic structure, not arbitrary-precision
bit operations or process memory. No partial count is returned if any leaf
refuses.

To reproduce with a DIMACS file:

```bash
python -m scripts.eth_reference
python -m scripts.eth_reference --dimacs small.cnf --output evidence.json
```

A successful run writes `"status": "completed"`; capacity refusal emits
`"status": "capacity_refusal"`, `count: null` and exits 2. The default
threshold `M=2` is **experimental**, not the theorem's sparsification
parameter. These are finite certified *reference* constructions, with
potentially exponential work, strict resource limits, and no general
non-refusal or subexponential running-time claim. The literal theorem
admission remains a separate, fail-closed entrypoint.

The optional `summation='eliminate'` path uses the independently
certified group-factor elimination backend described above. The default
`'tuples'` retains the original explicit measurement-reference evaluator.
The CLI accepts `--summation eliminate`, and every result records the
selected backend, summation and construction parameters.

### Finite-size width audit of the actual swap/spectral auxiliary construction

The separate hand-certified clique witness above cannot establish what
the paper's *specific* construction does. A bounded follow-on probe now
uses `construct_bounded_designs` with the implicit spectral operator,
its true incidence-to-coordinate transfer, projector-based measurement
rows, and **exact conditional-expectations schedules** where feasible.
For each center, it independently invokes `certify_measurements` and
derives factor scopes from the verified nonzero lambda coefficients,
rather than simply assigning a group graph from the original CNF.

**Measured and certified** on GitHub Actions CPython 3.13 on
2026-11-09 (run `42682559085`, then integration run `42683146610`):

| CNF | Chosen r,Q,R | Exact schedule | Center group graph | Largest induced scope | Maximum measured rows |
|---|---|---|---|---:|---:|
| cyclic binary, n=6 | 2,2,2 | conditional | K2 at 1,2 | 2 | 2 |
| cyclic binary, n=6 | 3,2,2 | conditional | K3 at 1,2 | 3 | 4 |
| cyclic binary, n=8 | 4,2,2 | conditional | K4 at center 2 | 4 | 6 |
| cyclic ternary, n=9 | 3,3,2 | conditional | K3 at 1,2,3 | 3 | 8 |
| cyclic ternary, n=9 | 3,3,3 | conditional | K3 at 1,2,3 | 3 | 6 |
| cyclic ternary, n=9 | 2,6,1 | **digits** (demo) | K2 at 1..6 | 2 | 9 |

In the r=4 example, the first center had five of the six possible
edges and induced scope three groups; center two had all six edges,
induced scope four groups, and a largest possible dense domain of
2**8 Boolean assignments. The generated r=3,Q=3,R=2 case had all
three edges at **all** three centers, with the complete group scope
covering all nine variables. All the reported edges came from exact
nonzero cross-group polynomial values and independently verified
measurement witnesses.

A separate differential test fixes the **same conditional schedule**
and compares `measurement_basis='selectors'` versus
`measurement_basis='projector'`: their replacement polynomials,
per-clause foreign-group scopes, interaction edges, and maximum
induced-domain sizes agree. Projector compression changes the number
and coefficients of measurement rows, **not** the actual dependence
of a clause on a foreign group.

**Strict scope of the finding:** Every case above uses finite manually
chosen `r,Q,R`. The exact balancing implementation runs, but its
*lemma hypotheses are false* at these sizes (even when some observed
bounds happen to hold), and `audit_bounded_cnf` rejects the paper's
literal `n`-derived schedule. The `Q=6R` case is explicitly a
digit-schedule demonstration, not a paper-parameter construction.
This experiment therefore refutes a proposed **finite-size structural
heuristic** that spectral projector construction would automatically
make the group graph sparse. It does NOT refute the manuscript or
prove that an admitted asymptotic paper construction has large width.

As before, a complete group graph determines the graph's structural
treewidth, not a lower bound on the cost of every exact algebraic
contraction. Spectral cancellations, tensor factorizations, sparse
supports, or separable local factors may make a dense primal graph
easier than its naive dense tables.

Reproduce:

```bash
PYTHONPATH=src:. python -m benchmarks.eth.spectral_factor_width_probe
python -m pytest -q -m integration tests/eth/test_spectral_factor_width.py
```

The essential next question is **whether the admitted parameter
schedule gives additional algebraic structure beyond the small-row
and small-degree certificates**. Such structure must be measured or
proved independently; it cannot be inferred merely from the
number of measurement rows or the spectral construction's name.

### Exact clause-tensor contraction, with an exposed rank obstruction

The opt-in `eth/tensor_train.py` method
`contract_certified_order_zero(formula, design, replacements, at=center)`
evaluates the exact rational deformation value `H(center)`, using the
same separately verified `certify_measurements` contract as Taylor
evaluation. It is **not** a replacement for the positive-order
Taylor/Hermite pipeline: derivatives are not implemented here.

At a certified center, each signed literal's false-value is an additive
sum of functions of individual group assignments,

`f_(e,j)(x) = sum_g a_(e,j,g)(x_g)`.

The terms are computed directly from owner-local coefficients and the
certified foreign-group measurement lambdas. Thus

`clause_e(x) = 1 - product_j sum_g a_(e,j,g)(x_g)`.

A tensor train represents the unsatisfied-clause product by carrying a
subset `S` of literals whose contributing group has already been
selected. At group g, a transition `S -> T` (with S subset T)
contributes `product_{j in T\\S} a_(e,j,g)(x_g)`. The initial and
terminal states ensure each literal selects **exactly one** group.
A separate constant channel supplies the leading 1. Therefore **one
width-w clause has an exact representation with bond at most 2**w+1**
without enumerating the cross product of all its group assignments.
For 3-CNF this gives at most nine states, independent of r.

To contract the complete formula, tensor trains are multiplied
pointwise, then compressed using exact rational left/right rank
factorizations. No floating-point threshold or approximation is
permitted. The implementation tracks original and compressed bond
sizes, clause-by-clause bond history, core size, rational arithmetic
operations and maximum coefficient bits. `TensorLimits` bounds
groups, individual group-mask domains, clauses, measurements, bond
dimension, intermediate core entries, operations and coefficient bits.
Capacity refusals are explicit; the original Taylor evaluator
remains the independent correctness oracle. A local mask domain is
still `2**|group|`, so compact bonds do not remove all exponentials.

**Executed finite spectral evidence** (GitHub-hosted CPython 3.13,
one-off run `42686688802`): every tensor value matched the independent
exact separated Taylor value at the same center.

| Spectral CNF | Center | Certified group graph | Final exact tensor bonds | Peak clause-product bond |
|---|---:|---|---|---:|
| cyclic 2-CNF, n=6,r=3,Q=2,R=2 | 1 | K3 | 3,3 | 4 |
| cyclic 2-CNF, n=8,r=4,Q=2,R=2 | 2 | K4 | 2,4,4 | 4 |
| cyclic 3-CNF, n=9,r=3,Q=3,R=2 | 1 | K3 | 7,8 | 8 |

The K4 instance has dense group connectivity but non-maximal exact
tensor rank. The n=9 case nearly saturates its local eight-state
boundary, showing no universal rank reduction from the spectral
construction at these sizes. The tensor benchmark measured 0.177 s
on the K4 instance and 0.964 s on the n=9 center-1 instance under
Python `tracemalloc`; these are construction plus contraction
times, not a demonstrated speedup over variable elimination.
None of these inputs meets the literal paper parameter admission.

**Independent exact bond obstruction:** For the width-two formula

`F_k = AND_{i=1..k}(x_i OR y_i)`,

the central cut of the order `x_1,...,x_k,y_1,...,y_k` has truth
matrix `[[0,1],[1,1]]**(tensor k)`. Its determinant is nonzero,
so its exact matrix rank, and hence the minimum bond of any exact
tensor train at that cut, is `2**k`. Merely interleaving each x_i
with its matching y_i yields maximum bond 2 while preserving the
exact count `3**k`. GitHub run `42687252831` verified k=1..4
with rank progression 2,4,8,16 versus 2,2,2,2 and all correct counts.
This is an ordering-sensitive representation lower bound, **not** a
#SAT hardness lower bound, and not a counterexample to the paper's
particular spectral construction.

Reproduce:

```bash
PYTHONPATH=src:. python -m benchmarks.eth.tensor_rank_probe
PYTHONPATH=src:. python -m benchmarks.eth.tensor_bond_obstruction
python -m pytest -q tests/eth/test_tensor_train.py tests/eth/test_tensor_bond_obstruction.py
```

The remaining question is whether an exact contraction ordering and
the specific spectral coefficients jointly keep intermediate tensor
ranks and local summation costs subexponential under the manuscript's
**admitted** parameters. The finite results above establish neither
that bound nor a practical worst-case implementation.


A second matched, single-run benchmark (GitHub Actions
`42688123022`, Python 3.13) measured the tensor path and the
existing exact factorized Taylor evaluator under the **same**
`tracemalloc` setup, after tightening rational-operation accounting.
On cyclic 3-CNF with n=9,r=3,Q=3,R=2:

| Center | Tensor seconds | Factorized Taylor seconds | Tensor traced peak | Factorized traced peak |
|---:|---:|---:|---:|---:|
| 1 | 0.552 | 1.277 | 426,640 B | 995,060 B |
| 2 | 0.433 | 1.157 | 324,648 B | 896,972 B |
| 3 | 0.281 | 0.865 | 216,936 B | 673,092 B |

The n=8,K4 center-2 case measured 0.088 versus 0.095 seconds.
These are one-run comparisons, not stable microbenchmark medians.
They establish that the tensor representation can produce actual
small-instance arithmetic savings, not that it is the best default
or the paper's runtime result. Python remains the reference; no
unproved native-kernel cutover is made.

### Exact tensor Taylor jets over a truncated polynomial ring

The opt-in module `eth/tensor_jet.py` extends the independently
certified order-zero tensor train to the exact local ring

`A_J = Q[z]/(z**(J+1))`.

`contract_certified_taylor(formula, design, replacements, at=t,
order=J)` returns the **complete coefficient vector** of
`H(t+z) mod z**(J+1)`, with per-clause bond history, exact arithmetic
work and coefficient bit limits. Unlike the paper's Boolean-difference
Taylor identity, this evaluator **directly shifts the original
replacement coefficient polynomials** and assembles each signed
literal as the sum of its group-local polynomial contributions.
Every design is independently certified at the chosen center, but
the varying derivative coefficients are not required to lie in the
center's measurement rowspace. This is a different exact evaluation
path, not a proof of the paper's bound.

**Why rational RREF is not valid.** The jet `z` is nonzero but
noninvertible in `A_J` when J>=1, so selecting pivots from only
the constant coefficient can silently discard a nonzero derivative.
The exact jet factorization in `_jet_column_factor` uses a minimal
z-adic valuation pivot `p=z**v*u(z)`, where the unit part satisfies
`u(0)!=0`. Every entry of the current pivot row has valuation
at least v and is divisible by p in the quotient ring. Its quotient
is computed by finite power-series division by **u**, never by
the nilpotent z**v. Subtracting the outer product of that column
and quotient row clears both its pivot row and column exactly.
Repeated extraction yields an identity `M=U*V` in `A_J`, even
for all-zero constant coefficient matrices. The process uses at most
`min(rows,columns)` nonzero factors; it does **not** prove the
smallest possible module bond rank.

Both left and right tensor compression sweeps use this exact
ring identity. Every product is truncated after degree J; no
floating-point rank threshold or division by a nonunit occurs.
`TensorLimits` additionally bounds Taylor order, replacement
degree and the aggregate coefficients stored in a tensor core
or factor matrix. These supplement the original bond, group-mask,
rational-operation and coefficient-bit limits. All exhausted
budgets refuse the operation.

The separate
`count_origin_from_tensor_designs(formula, centers, replacements,
order=J)` runs that exact tensor-Taylor computation at each supplied
nonzero center, then passes its jets to the independently developed
count-only Hermite CRT. A **proved degree upper bound** from the
replacement polynomials and **strictly more Hermite conditions**
than that degree are required before any work. The result is
range/integrality checked against `[0,2**n]`; it neither executes
the Boolean-cube counting oracle nor substitutes an unjustified
degree bound. It remains an *explicit alternative*; the existing
Boolean-difference `taylor_coefficients_separated` and
`count_origin_from_manual_designs` APIs are unchanged.

**Exact validation** on GitHub Actions, CPython 3.13, workflow
`42698224532`: 21 targeted tests passed, with strict production
typing. These include seeded rectangular nilpotent matrices,
constant-zero derivative-nonzero factors, complete degree-two
deformations against *both* independent separated Taylor and
exhaustive deformation-polynomial oracles at multiple centers and
orders 1,2,3, actual spectral-projected constructions, Hermite
origin recovery using different centers, and explicit budget
refusals. A nilpotent count case with
`P(T)=1-T` at center `t=1` has Taylor data `(0,-2)` and
correctly reconstructs two satisfying assignments at T=0.

**Measured costs** from run `42697587887` (single GitHub-hosted
runner, Python 3.13, independent `tracemalloc` tracing for each
method, no speedup extrapolation):

| Input | Order J | Final exact bonds | Tensor seconds | Separate Boolean-difference seconds | Tensor peak traced B |
|---|---:|---|---:|---:|---:|
| manual 4-variable degree-two deformation | 0 | 4 | 0.125 | 0.020 | 178,442 |
| manual 4-variable degree-two deformation | 1 | 4 | 0.187 | 0.111 | 202,200 |
| manual 4-variable degree-two deformation | 2 | 4 | 0.222 | 0.221 | 156,116 |
| manual 4-variable degree-two deformation | 3 | 4 | 0.286 | 0.348 | 274,096 |
| real 6-variable spectral construction | 0 | 3,3 | 0.335 | 0.033 | 120,160 |
| real 6-variable spectral construction | 1 | 4,4 | 0.522 | 0.250 | 143,616 |
| real 6-variable spectral construction | 2 | 4,4 | 0.597 | 1.046 | 148,504 |

The spectral example at J=2 shows ~1.75x lower measured runtime
than the reference, but the reference wins at J=0 and J=1. The
tensor path had **larger traced Python memory use in every case**.
The four-variable deformed input reached 1,802-bit intermediate
rational coefficients at order 3; limiting only bond dimension
is therefore insufficient. All measured values matched the
independent exact reference coefficient-by-coefficient. This
neither proves speed at higher J nor admits the literal
n-derived paper parameters.

Reproduce:

```bash
PYTHONPATH=src:. python -m pytest -q tests/eth/test_tensor_jet.py
PYTHONPATH=src:. python -m benchmarks.eth.tensor_jet_probe
```

The remaining main risk is that intermediate polynomial bonds
or rational coefficient bits grow too quickly as n and J increase.
The tensor path does not yet improve the paper's asymptotic
worst-case claim, even where it wins a finite instance.

### Three exact contraction strategies on identical CNF families

`benchmarks/eth/three_way_contraction.py` measures three exact,
independently executable ETH Taylor evaluation strategies on the
**same canonical CNF, same degree-one replacement polynomials, same
variable partition, same certified integer measurement rows, same
center t=1, and same Taylor order J**:

1. `summation='eliminate'`: the complete Boolean differences
   followed by group-mask factor elimination, with scopes counted
   in **groups** and physical mask domain `2**|S_g|`
2. `summation='fused'`: exact difference fusion followed by
   elimination of factors over original Boolean **variables**
3. `contract_certified_taylor`: exact truncated polynomial
   tensor-train clause automata, compression by valuation-safe
   rational jet module factorization, and summation over group masks

The input families have two Boolean variables per group, and
`P_e,l(T)=(1+T/7)*x_l` for every literal occurrence. Thus every
deformation reduces exactly to the original CNF at T=0, including
negative literals. Independent **exhaustive #SAT** checks each test
case up to 12 variables and is not used inside any production
evaluator. For n<=6 the independently evaluated full Boolean-cube
deformation polynomial also checks each returned Taylor coefficient.
Every other completed arm is checked coefficientwise against its
independently implemented peers. Refusals remain explicit.

Families include independent 2-clauses, a path of 2-clauses, an
all-to-all positive clause graph among group boundary variables,
a signed implication path, and a matching graph with both
**separated** and **interleaved** group orderings. The matching
variants use the **identical CNF and replacement polynomials** but
different group orders. Both variable-elimination approaches
remain low-width; tensor contraction can require exponentially
different exact bonds at the bad versus good cut.

**Executed GitHub-hosted reference evidence** on 2026-11-09:
workflow `42701048824` (initial 15 cases, 24 tests and
strict mypy across 75 source files passed), then extended workflow
`42701715939` (24 cases, **28 tests passed**, strict mypy passed).
Runs used CPython 3.13 and Python `tracemalloc`, with each arm
measured separately after a garbage collection. Formula construction,
the independent oracle and the family-generation setup are
excluded from per-arm times, while center certification **is**
included. Single-run timings are not robust performance medians.

| Family | n | J | Group masks seconds | Fused variables seconds | Tensor jets seconds |
|---|---:|---:|---:|---:|---:|
| independent | 6 | 2 | 0.478 | **0.023** | 0.227 |
| positive path | 6 | 2 | 0.799 | **0.015** | 0.159 |
| clique | 6 | 2 | 1.255 | **0.021** | 0.276 |
| signed path | 8 | 1 | 0.389 | **0.024** | 0.356 |
| clique | 10 | 1 | 4.766 | **0.098** | 2.089 |
| clique | 12 | 0 | **refused** | **0.158** | 3.524 |
| matching, separated order | 12 | 0 | 0.046 | **0.030** | 1.094 |
| matching, interleaved order | 12 | 0 | 0.047 | **0.030** | 0.539 |

The 12-variable clique triggered `ETH Taylor factor table
entry limit` under the fixed **256-entry** group-factor cap.
The fused-variable evaluator retained no more than **32** factor
entries; the tensor path completed with maximum final bond six.
This is a genuine difference in finite representation costs under
the chosen contracts, not a hardness separation or evidence that a
generic variable-factor approach is polynomial time.

On the matching formula, the exact count is **1,728** in both
orders. Tensor final maximum bond was **8** with all left
groups first, versus **2** with paired interleaving. Fused
variable-factor work was **414 charged units** in both orderings,
while tensor work fell from **33,396** to **16,100** charged units.
The underlying matrix-rank obstruction is described earlier:
an exact bond across the separated matching cut has rank 2**k;
interleaving removes that particular width growth. This does
not prove a lower bound for arbitrary contraction order.

**Algebraic and operand-dependent bit accounting (replaces the
obsolete maximum-bit proxy):** Every completed result records its
scope basis; peak retained factor entries or tensor bonds/cores;
charged logical arithmetic work, maximum rational coefficient bits,
exact Taylor coefficients, elapsed time and traced Python allocations.

The earlier `charged_work_units * max_coefficient_bits**2` diagnostic
has been **removed** from the benchmark. Those counters charged
different logical units, and even a correct square bound at the maximum
bit width would not count the actual integer operands or normalization.

The new `benchmarks/eth/rational_bit_accounting.py` runs each
completed exact evaluator a **second time outside the timed and
tracemalloc-measured region**. An exact Python profiling hook observes
every invoked `Fraction` arithmetic primitive and its real signed
integer numerator/denominator operands, including work performed
during measurement certification and tensor rank sweeps. An
**independent integer-only reference replay** reconstructs the reduced
result for every rational addition, subtraction, multiplication,
division and integer-pair construction. Every replay result is checked
exactly against the value returned by Python Fraction; mismatches,
unmodeled methods, unsupported constructor types and unavailable
hooks cause a hard failure, not a plausible-looking zero.

The replay charges the following **constructive schoolbook bit-step
upper bounds for the specified integer arithmetic algorithm**, using
the actual bit lengths a,b of the operands at *each* integer step:

- integer addition/subtraction: `4*(max(a,b)+1)`
- grade-school integer multiplication: `8*(a+1)*(b+1)`
- shift/subtract integer division/remainder: `64*(a+1)*(b+1)`
- Euclidean gcd: the **sum of the individual charged division steps**
  obtained from the actual Euclidean remainder sequence, not a
  single assumption based on the maximum numerator size

That is a value-dependent, executable witness for a conservative
upper bound on the bit steps of a **specified rational reference
arithmetic implementation** following the observed operation sequence.
It includes rational normalization, all recorded intermediate integer
sizes, exact Euclidean iterations, constructors and supported
comparisons. Unlike the old proxy, the bound varies with *actual
operands*, even for two calculations with the same number of
logical jet operations and the same algebraic graph. Each strategy
reports primitive call counts, integer adds/multiplications/divisions,
gcd calls, gcd quotient/remainder steps, peak intermediate integer
bits, and the summed reference bit-step bound.

**Do not expand the claim:** This is NOT measured machine bit
instructions for CPython, a hardware-independent upper bound on
CPython's bigint implementation, nor a rigorous whole-program
bit-complexity bound. Raw integer operations *outside* Fraction,
hashing, object allocation, Python control flow, memory management,
and refusal paths are excluded. The three exact strategies use
different Python code and can perform untracked structural work.
The report contains explicit `bound_is_for_complete_algorithm=false`
and `bound_is_for_actual_CPython_machine_execution=false` fields,
plus `bare_integer_and_nonFraction_arithmetic_unaccounted=true`.
A capacity refusal has **no invented bit-step bound**. The historical
logical-operation counters remain separate. Traced Python allocations
from `tracemalloc` are not total process RSS.

**Fixed resource policy:** both classical factor routes use the same
factor entry, total entry, work, jet-operation and rational-bit
limits. Tensor contraction uses its own bond, core-entry,
jet-coefficient-entry and rational-operation limits plus the
same coefficient-bit ceiling. Factor entries and tensor bonds
have different units and cannot share a meaningful numeric cap.
All capacity refusals are recorded with exact reasons, and
unexpected exceptions or coefficient mismatches fail the benchmark.
The integration tests also force all three methods to refuse
under individually tightened capacity limits. No method silently
switches to brute force.

**Claim boundary:** These are manually certified balanced designs.
None meets the manuscript's full n-dependent schedule; the
all-positive clique formulas have growing literal occurrences and
are not used as bounded-occurrence theorem instances. The small
size and changing Taylor order also prohibit extrapolating the
table as an asymptotic rate. The observed fused-variable advantage
is evidence for a better *current reference implementation* on
these families, not a non-exponential worst-case #SAT result.
The tensor result remains valuable as an independent algebraic
representation and as an order-sensitive rank probe.

Reproduce:

```bash
PYTHONPATH=src:. python -m pytest -q tests/eth/test_three_way_contraction.py
PYTHONPATH=src:. python -m benchmarks.eth.three_way_contraction
```

The command emits machine-readable JSON for each family,
including witnessed reference-rational bit costs when the evaluator
completes. A true **whole-algorithm** bit-complexity certificate still
requires tracking all non-Fraction big-integer operations, total
retained algebraic storage, Python-independent control-flow
operation bounds, and growing-order tests under a fixed regime.
No argument about asymptotic ETH complexity follows from the
measured finite traces. Keep all three exact methods opt-in.
