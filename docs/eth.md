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
