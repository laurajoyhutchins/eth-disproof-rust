# Complete theorem acceptance: independent proof gates

**Status: RED, deliberately and for multiple independent reasons.** The source of the opt-in acceptance test is `research_acceptance/test_complete_bit_recurrence.py`. The companion logic lives in `reference/complete_theorem_gate.py` and `reference/cell_rate_transfer.py`. Green finite tests verify **that the gate rejects unsupported claims**, not that a non-exponential generalized-Sudoku algorithm has been proved.

Run the gate and symbolic-rate regression tests normally:

```bash
PYTHONPATH=src:. python -m pytest -q tests/unit/test_complete_theorem_gate.py tests/unit/test_cell_rate_transfer.py
```

Run the complete theorem acceptance **explicitly** (expected to fail at the final theorem test):

```bash
PYTHONPATH=src:. python -m pytest -q -o addopts='' research_acceptance/test_complete_bit_recurrence.py
```

The acceptance requirements are intentionally independent:

1. **Complete local bit work:** every frame term, including canonicalization, oracle callbacks, planning and allocation, must be justified by a universal source-linked cost lemma. `LocalBitBound` merely checks a numerical dictionary's shape. Supplying invented positive integers is **not** a proof.
2. **Source correspondence and totality:** `reference/whole_frame_recurrence.py` tracks open source/totality premises, including non-refusal, working-set bit accounting and all generated-oracle operations. The full test must reject the current implementation even if every `LocalBitBound` entry is supplied.
3. **Sudoku-cell parameter:** a bound `log2 T(s) = O(s (loglog s)^beta / (log s)^alpha)` and an encoding using `s=Theta(N (log N)^delta)` transfer to `log2 T(N)=o(N)` from this upper bound only when `alpha>delta` or `alpha=delta` and `beta<0`. The tightened depth-sensitive conditional parameters are `alpha=1/2, beta=0`, whereas the direct Sudoku encoding has `delta=1`. Consequently the *displayed upper bound* is too weak to establish subexponential behavior in the number `N` of Sudoku cells.

The sharpened support summation and the restricted three-copy interface cut are proved in [depth-summed-paper-support.md](depth-summed-paper-support.md). The last conclusion is about the available **proof bound**, not a lower bound on the solver. An algorithm might be faster than a loose upper bound suggests. For the explicit growing box-order family `b=2**k`, one has `N=2**(4k)`, `M=6kN`, and `lambda=ceil(log2 M)<=10k`. Hence

\[
\left(\frac{M}{N\sqrt\lambda}\right)^2
=\frac{36k^2}{\lambda}\ge\frac{18}{5}k\longrightarrow\infty.
\]

A proof of `2**o(s)` measured in Boolean network edges does not by itself discharge the stronger `2**o(N)` cell claim for this reduction.

`CompleteTheoremStatus.require_complete()` reports *all current blockers* instead of raising only on the first missing local term. It obtains the source/totality blockers from the composed recurrence's `OPEN_PREMISES` and the cell-transfer gap from the actual published rate and reduction. There is no caller-supplied boolean that makes these obligations vanish. This is an engineering guard, **not** a formal proof checker: future positive results must update the independent mathematical source proofs, their implemented correspondence, and the gate together.

The single complete-theorem test remains **unskipped and un-xfailed**, outside ordinary checkpoint CI. It cannot be marked green merely by filling local cost fields. A non-refusing worst-case theorem, its bit-operation recurrence, and its claimed input-size parameter must be established independently.


## Paper-to-Lean-to-Python audit: first decisive unclosed cost

**Source pin:** original [October 25 manuscript](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex), [Lean endpoint](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean), [Lean scope note](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/378.md). The pinned Lean file constructs a primitive `BitProgram.Program 80 1220` via `NativeLargeEntry.run` and proves its exact result, time, and all-prefix visited space. The formal scope note gives a `(log log n)^2` numerator in the exponent; the October 25 manuscript advertises the sharper `log log n` numerator and a separate sparse-instance improvement. **Neither source identifies that primitive machine with the Python `ContractionEngine` or `eth/` implementation.** This is the *first source-correspondence gap*, not evidence that the upstream Lean theorem is false.

| Stage | Source route | Verified here | Still missing from this implementation |
| --- | --- | --- | --- |
| Input and parameters | `eth/parameters.py` and the manuscript Step 5 | Symbolic sufficient inequalities and one physical balancing-lemma example ([admission witness](eth-paper-lean-admission.md)); explicit canonical CNF semantics | A complete, source-equivalent, **total** input-to-count path using the literal schedule; no huge instance is physically materialized |
| Spectral construction | `eth/construction.py`, `ImplicitAuxiliaryDesign.row_at` | Requested spectral coefficient heights, restricted projector entries, and final output coefficient height ([implicit-height proof](eth-implicit-spectral-height.md)); these need not materialize dimension `D` | Whole-construction and strict selector-route costs; the independently certified projected Gram/RREF bit bound covers the **projector** representation, not a strict-selector cutover |
| **Exact center / Taylor data** | `eth/factorized_taylor.py`, `eth/interpolation.py`, `eth/tensor_jet.py`, and `count_from_constructed` | Exact small-case differential oracles, some source-derived support/width **upper certificates**, output coefficient bit bounds | **A universal source-correlated bound on every intermediate representation, work and retained memory for all coupled inputs under paper-admitted parameters.** This is the first *algorithmically decisive* missing bound after the algebraic setup. |
| Appendix D alternative | `contraction/engine.py`, `PacketEntry`, `reference/whole_frame_recurrence.py` | Conditional calls, support, individual arithmetic and several source-loop envelopes | Closure and bit cost of **all generated entry oracles**, including numerical-exception leaves, as well as total non-refusal. The Appendix D path must not be conflated with the main-body spectral code. |
| Readout / theorem | `recovery/`, exact counters, `research_acceptance/test_complete_bit_recurrence.py` | Conditional Hermite arithmetic, finite exact counts, a total **exponential** reference, intentionally red theorem gate | A complete bit-operation recurrence and worst-case space proof; for generalized Sudoku, transfer from network edges `s=Theta(N log N)` to cells `N` |

The first row's source-correspondence problem is categorical: a
validated Python result does **not** certify a Lean primitive step.
The center-evaluation row is the first substantial *intermediate
representation* problem on the Python main-body research route.
Earlier local obligations in balancing, strict-selector construction,
and source correspondence remain. The projected Gram/RREF bit bound
is now certified for the projector representation (see below);
calling center evaluation 'first decisive' does not erase those other gaps.

### A nontrivially coupled family meeting the same paper assumptions

The former complete symbolic Step-5 witness was
`AND_i x_i`, whose factors are independent and whose count is 1.
That family can make contraction look easy for the wrong reason.

The executable `virtual_coupled_3cnf_step5` now certifies, without
forming an enormous integer `n` or constructing its clauses, the
**connected** family for `n=2**lambda`:

```
F_n = AND_{i in Z/nZ} (x_i OR x_(i+1) OR x_(i+2))
```

For `n>=8`, the `n` clauses are distinct, every clause has
three literals and every variable occurs in precisely three
clauses. Thus `M=3n,b=w=3`. The paper's balancing inequality
`2(b+w)D**2<=M` becomes `12D**2<=3n`, **equivalent to**
`4D**2<=n`, the sufficient inequality already checked by the
independent-unit certificate. All other Step-5 inequalities are
unchanged. Hence at `lambda=2**34` the coupled family also
satisfies *every source-pinned sufficient admission inequality*,
with exactly `r=113, Q=3,947,580, R=524,288`. This is not a
finite-time evaluation, a proof of small rank or a bound on a
center's work. The corresponding small cyclic `CNFFormula`
objects are independently checked for normalization and incidence.

The same numeric admission argument applies to **any** family of
three-permutation clauses `(x_i OR x_pi(i) OR x_sigma(i))`
where every clause has distinct literals and no clauses are
duplicate or subsumed: bijective incidence gives `b=w=3,M=3n`.
This permits strongly coupled interaction patterns. The cyclic
example is an explicit, easy-to-describe witness, **not** a
worst-case hardness instance or evidence of a uniform rank bound.

### One smallest falsifiable next mathematical experiment

Do **not** tune Sudoku frontier orbits for this purpose. Take the
source's exact center evaluator and **one** fixed deformation
center and Taylor coefficient order for the three-permutation
3-CNF family. State a candidate compressed intermediate
representation and prove an operation-by-operation invariant:

1. The representation is exact and closed under every factor
   multiplication, summation and derivative/coefficient update
   the chosen source evaluator actually performs, for **arbitrary
   permitted permutations**, not just the cyclic example.
2. Its **total creation/work count** and all intermediate
   coefficient bit lengths fit a source-backed
   `2**o(n)` bit-work envelope. If targeting the published
   endpoint, explicitly account for the intended
   `2**O(n (loglog n)**2/sqrt(log n))` Lean-scale exponent
   or the sharper manuscript bound, without substituting a
   microbenchmark fit.
3. Its *simultaneously retained* memory meets the claimed
   polynomial-space requirement. Polynomial-height **final**
   coefficients alone do not establish either claim.
4. Run the same operations on small normalized, coupled formulas
   and compare all outputs with an independent exact oracle.
   These finite examples detect incorrect algebra; they do **not**
   certify the universal bounds.

**Success** means a proven source-correlated closure and cost
invariant for the *entire chosen center evaluation*; then the
remaining center count, Hermite readout and whole-input totality
can be composed. **Failure** means an explicit source input
whose intermediate representation exceeds the **proposed**
bound, or a missing bound at one precise operation. Either is a
useful mathematical outcome. An observed low-rank center,
a virtual admitted parameter tuple, a numerical `LocalBitBound`
dictionary, and a red capacity check are **not** substitutes.

### Bounded fused-center falsification: what the source actually charges

[The source-correlated coupled probe](../benchmarks/eth/coupled_fused_probe.py)
and [its independent tests](../tests/eth/test_coupled_fused_probe.py)
resolve **one restricted question**, not the whole center closure theorem.
Both families have `n` distinct three-positive-literal clauses, with
every variable appearing in exactly three clauses. They use the exact,
nonconstant occurrence substitution
`P_e,v(T)=(1+T/7)*x_v`, center `t=1`, Taylor order `1`.

The finite experiment uses a **manually certified single-group,
zero-measurement design**, not a full paper-admitted `r,Q,R` spectral
construction. The full Step-5 symbolic admission proved above still
applies to suitable three-permutation families at astronomical `n`;
it does **not** license treating these finite runs as paper executions.

The probe derives factor support from the *truncated polynomial
coefficients* and follows the very same smallest-union-scope variable
choice used by `eth/fused_taylor.py`. It calls the existing
`certify_dense_order` proof reference to compute every input table
and every joined Boolean assignment domain **without** creating any
large tables. Whenever the concrete evaluator completes, the tests
check that its *actual* `factor_scope_peak` and
`factor_assignments_tested` equal the independently computed
source-geometry certificate.

| Variables | Cyclic max joined width | Shuffled max joined width | Shuffled maximum dense joined assignment domain |
| ---: | ---: | ---: | ---: |
| 8 | 5 | 5 | 32 |
| 12 | 5 | 7 | 128 |
| 16 | 5 | 7 | 128 |
| 32 | 5 | 14 | 16,384 |
| 64 | 5 | 27 | 134,217,728 |
| 128 | 5 | 54 | 18,014,398,509,481,984 |

The shuffled third permutation is produced deterministically from
seed `20261109+n` with independently checked distinct-literal and
three-occurrence conditions. The numbers are **finite reproducible
samples**, not a proved `Omega(n)` treewidth or rank lower bound
on all choices of three permutations.

At `n=32`, the *actual* fused center evaluator under a
1,024-entry factor cap **completed** on the cyclic input and
**refused** on the shuffled input with a factor-entry limit. The
uncapped *structural* audit of the latter reports a maximum joined
Boolean domain of 16,384, but does **not** claim it was allocated.
For `n=64,128`, the audit is **structural only**. On completed small
runs, the full exact jet agrees with an independent full-cube
calculation. For the cyclic family it also agrees with an
independent **four-state transfer matrix**, showing that the
correct answer does not intrinsically require the dense tables
of an unfortunate representation.

[Opt-in exact integration and JSON evidence, GitHub run 42730858967](https://github.com/laurajoyhutchins/nonexp-sudoku/actions/runs/42730858967)
passed all three research integration cases and emitted all twelve
cases; source-matched checkpoint contracts also passed. The
ephemeral verification workflow is **not** retained in the repo.

**Consequence:** The current fused dense-table representation does
not establish uniformly compact exact-center intermediates for
bounded-occurrence coupled inputs. Even at fixed width three, its
greedy joins can grow sharply. This does **not** contradict the
OpenAI paper's different algebraic construction, the Lean theorem,
a potential symbolic quotient, or polynomial-space counting
for another algorithm.

The *remaining* open obligation is not to tune this greedy
elimination order. It is to find and prove a source-faithful,
**closed** intermediate algebraic representation for the admitted
coupled main-body construction, with bounded *total* bit work
and polynomial **simultaneous** retained space. Once that exists,
audit center count, Hermite readout, source refinement and
all-input totality separately.

Existing acceptance remains intentionally **RED**. No independent
theorem registry, scheduler or additional CI workflow is needed.

## Conditional bit-work and streaming-space bound for one separated spectral center

The [source-correlated mathematical reference](../reference/eth_separated_center_budget.py)
addresses a **different** representation from the dense fused
factor-table obstruction above: the original `eth/taylor.py`
`summation='tuples'` algorithm, **after** a valid
`MeasurementCertificate` has been supplied.

For a normalized CNF with `n` declared variables, `m` clauses,
`ell` literal occurrences, Taylor order `q<=n`, and a
certified measurement design with `r` groups of sizes `g_i`,
`s` total measurement rows and maximum row L1 norm `D`, put

```
P = sum_{j=0}^q binom(n,j)*2**j
Y = (2*D+1)**s
A = sum_i 2**g_i
W = sum_i (number of clauses owned by group i)*2**g_i
```

These are **source-loop** quantities, not a hypothesized tensor rank:
`taylor_coefficients_separated` invokes exactly `P`
`restricted(E,U)` calls; for each one, the tuple evaluator
visits at most `Y` shared measurement vectors and at most
`A` group masks per vector. Therefore the group-mask visit
ceiling is `P*Y*A`, and the number of per-clause factor
evaluations is at most `P*Y*W`. Early zero exits only lower
the observed work. Source tests independently compare completed
spectral executions' recorded counters to these ceilings.

### Rational coefficients: the missing factor-table height is not needed

Let `d` be the maximum degree of a transferred replacement
coefficient polynomial; let `K` count **all** rational input
coefficients, the center, and the independently certified
local/lambda witness entries. Let `B` bound their numerator
and denominator bit lengths. The product `H` of their
denominators has `log2 H <= K*B`.

The source computes shifted coefficients of `P(t+z)` using
Horner arithmetic. Every shifted coefficient's denominator
divides `H**(d+1)`. The `U`-specific corrections are sums
of at most `n` shifts; the source's scalar base terms sum
at most `n+s` rational entries, each measured integer being
bounded by `D`. Consequently every linear literal jet has
denominator dividing `H**(d+1)`.

Every clause is a product of at most its literal count of
these jets; across the entire CNF, no term multiplies more
than `ell` literal jets. All partial products and sums
therefore live on the *same* rational denominator lattice
`H**((d+1)*ell)`. Truncated jet multiplication introduces
at most `(q+1)**ell` coefficient-index combinations.
The nested sums over masks, measurement vectors and
`(E,U)` add at most `n+ceil(log2 Y)+ceil(log2 P)`
bits of numerator height. The explicit conservative bound
`every_intermediate_fraction_bits_upper` composes these
sources, rather than relying on final-output height alone.

The reference charges all source-local precomputation, each
pair, each measurement loop and each group/clause visit with
a deliberately loose polynomial multiplier for coordinate
work and schoolbook rational normalization. Its
`abstract_schoolbook_bit_work_upper` is a ceiling for that
**specified mathematical schoolbook cost model** conditional
on the supplied certificate and input scalar heights,
not measured CPython machine bit instructions or proof
of the certificate-generation runtime.

### Memory correction found in the source

The former expression `itertools.product(range(-D,D+1),repeat=s)`
internally materialized an input pool of `2D+1` integers
**before yielding the first measurement vector**. The
production tuple evaluator now uses
`_measurement_vectors(D,s)`, a lexicographically identical
odometer whose simultaneous state holds `O(s)` integers.
A test requests the first three tuples for `D=10**100`
without creating the range pool. This is an actual
source-level memory improvement, not an asymptotic runtime
claim.

The other live objects consist of the `O(ell*n)` source
replacement and shifted-polynomial entries, the certified
measurement matrices and witnesses, at most a configured
number of `U`-correction entries (64 by default), and
current `q+1`-coefficient jets. The bound
`retained_rational_slots_upper` is deliberately slack;
multiplied by the common bit-height ceiling, it gives
polynomial **mathematical coefficient** storage whenever
the source input/certificate parameters are polynomially
bounded. It is not a byte-perfect CPython heap model.

### What the literal Step-5 inequalities would give

Under the *actual* manuscript quantitative conditions

```
q <= 3*n*R/Q          delta = 3*R/Q <= 1/2
s <= 2*n/(r*lambda)   D <= r**(2Q)
max(g_i) <= 2*n/r     lambda = ceil(log2 n)
```

the source-loop exponent satisfies the conservative bound

```
log2(P*Y*A) <= n*Gamma + ceil(log2(n+1)) + ceil(log2 r)

Gamma = delta*ceil(log2(6/delta))
      + 2*(2*Q*ceil(log2 r)+2)/(r*lambda)
      + 2/r.
```

The first inequality follows from
`binom(n,j)*2**j <= (2*e*n/j)**j` and `2e<6`
for `j<=q<=n/2`, then
`P<=(n+1)*2**(n*delta*ceil(log2(6/delta)))`.
The remaining terms charge **all** measurement signatures and
the **sum**, not product, of independent group-mask domains.

For the source's literal
`r=floor(sqrt(lambda)/nu**2)`,
`Q=floor(lambda/(128*nu))`,
`R=4*ceil(sqrt(lambda))`, `nu=ceil(log2 lambda)`,
`Gamma=O(nu**2/sqrt(lambda))=o(1)`. This is a
conditional `2**o(n)` **one-center loop and abstract bit-work
bound**, if the supplied certificate has polynomial-height
entries and satisfies all quantitative inequalities.
There is no hidden large Boolean table.

The numerical caveat matters: the first symbolically admitted
coupled family at `lambda=2**34` has `q/n<=0.39844`
and this conservative `Gamma>1.61`. The upper bound
does **not** certify a finite practical speedup even for
an astronomically large input. At `lambda=2**50`,
the same coefficient of `n` is below `0.028`,
but `n=2**lambda` is even less physically representable.
These are exact symbolic **upper-rate** computations, not
runs of the paper algorithm and not runtime lower bounds.

### What is still unproved

This result **does not** certify a full input-to-count algorithm.
Most importantly, strict paper admission currently does not
prove that *every* source-transferred selector/projector design
meets the quantitative row-count and coefficient-height
conditions without resource refusal. Constructing the
conditional-expectation schedules, obtaining a sound actual
measurement certificate, and proving all their source-level
bit costs are separate tasks. So are the complete number
of centers, Hermite readout, disjoint sparsification,
finite-boundary handling, and refinement to the pinned
Lean primitive machine. The complete theorem gate remains
**RED**.

## A total exact baseline that does not prove the target theorem

`reference/total_exact_cnf.py` provides a separate, **total mathematical
reference kernel** for exact #SAT on already-normalized `CNFFormula`
inputs. It performs ordinary, fixed-variable-order dense factor
elimination using nonnegative integer counts. There are **no configured
capacity refusals** or conditional unproved black-box oracles in the
algorithm. On finite hardware an enormous table can still exhaust
memory; mathematical totality does not mean physically runnable for
arbitrarily large inputs.

This makes one complete, explicit bit-machine complexity upper bound
available as a control. It is not a bound for the paper's algorithm.

For an input with `n` Boolean variables, `m` normalized clauses,
and maximum clause width `w<=n`, define

\[
B=n+\lceil\log_2(m+n+3)\rceil+
\lceil\log_2(w+2)\rceil+8.
\]

The symbolic envelope `total_reference_envelope(n,m,w)` reports
ceilings corresponding to

\[
T_{\mathrm{reference}}\le
2^{n+16}(m+n+3)^2(n+w+3)^2(B+1)^2,
\]

and bit-cell storage

\[
S_{\mathrm{reference}}\le
2^{n+12}(m+n+3)(n+w+B+5).
\]

**Why these bound the abstract algorithm:** A factor table entry is
the number of assignments of a set of previously eliminated
variables satisfying a disjoint subset of the original clauses.
Factor ownership partitions both those clauses and those eliminated
variables. Multiplication of factors and summation over the next
variable preserve this invariant. Every intermediate product is
therefore in `[0,2**n]` and uses at most `n+1` bits. At most
`m+n+1` factor tables and one output scratch table coexist, each
with at most `2**n` Boolean assignments. Clause construction has
at most `m*2**n*w` literal tests. Across `n` elimination rounds,
there are at most `2**n` assignments per round, no more than
`m+n` attached factors and at most `n` bit extractions per
factor index. Deterministic scope scans and all dense table
allocations have polynomial overhead. The explicit constants
cover these scans and the listed abstract word operations after
their expansion to schoolbook bit steps on `B`-bit operands.

The kernel records actual additions, multiplications, operand-aware
schoolbook charges, modeled scope/mask events, peak simultaneous
table entries and model bit cells. It checks its observed execution
against its independently computed symbolic envelopes. It does not
pretend those counters enumerate the native Python interpreter,
object allocation, DIMACS parsing, or the cost of normalizing an
arbitrary unvalidated CNF into the `CNFFormula` ABI. The proof
applies to the specified abstract dense-array algorithm; the
source is an executable reference implementation of that algorithm.

The tests compare exact counts with independent exhaustive enumeration
on adversarial small CNFs, including zero variables, empty clauses,
unconstrained declared variables, contradictions, signed literals,
dense interactions, and randomized formulas. They also compare this
total reference with the existing *capacity-limited* fused ETH
evaluator on an identity deformation. A real subcubic Sudoku
encoding can be fed into the symbolic envelope without running
its astronomical `2**n` computation.

**The exponent is still linear in n**. This reference therefore
provides a complete **exponential** bit upper bound, not a
non-exponential worst-case algorithm, no universal result for
arbitrary vertex-oracle networks, and no `2**o(N)` Sudoku theorem.
In particular, it cannot be substituted as the missing
`LocalBitBound` of the paper schedule. The existing
`research_acceptance/test_complete_bit_recurrence.py` stays RED
and `OPEN_PREMISES` stays unchanged.

A separate **dense-representation obstruction** makes the problem
visible. For n=2k variables, take the CNF

```
F_k = AND_{1<=i,j<=k} (x_i OR y_j).
```

This is easy to count: it is equivalent to
`(AND_i x_i) OR (AND_j y_j)`, hence
`#F_k = 2**(k+1)-1`. Nevertheless, eliminating the x
variables first produces a factor on **all k y-variables**
at the very first step. The fixed-order dense reference therefore
materializes at least `2**k=2**(n/2)` table cells. A regression
test verifies this against the independent exact count.

This is a lower bound on **one representation under one ordering**,
not a lower bound on #SAT algorithms. The formula has a short
symbolic representation, demonstrating precisely why the right
algebraic abstraction matters more than more efficient allocation.

This isolates a precise research obligation: replacing the
`2**n` dense-table/assignment factor by a proved smaller total
representation in the admitted paper regime, without merely moving
its cost into coefficient bit lengths, a refusal cap, an oracle, or
the Sudoku-to-network parameter conversion.

Run:

```bash
PYTHONPATH=src:. python -m pytest -q tests/unit/test_total_exact_cnf.py
python -m mypy --strict reference/total_exact_cnf.py
```

## Universal final deformation coefficient height is polynomial

An unconditional, **representation-independent output-size lemma** now
has an executable reference in \`reference/eth_output_height.py\`,
with tests in \`tests/unit/test_eth_output_height.py\`. It applies
to **every** valid occurrence-specific rational \`ReplacementSystem\`,
including the actual spectral auxiliary replacements, at **every**
rational interpolation center. It does *not* require or imply
manuscript parameter admission.

Put \(n\) for declared Boolean variables, \(m\) for clauses,
\(\ell\) for total literal occurrences, \(d\) for the maximum
replacement-polynomial degree, and \(K\) for the total number of
explicitly stored rational polynomial coefficients, including
zeros. Let \(b\ge1\) bound the bit lengths of every input
coefficient numerator/denominator and the exact center's
numerator/denominator. Define

\[
  E=b(K+d),\quad C=n(d+1),\quad
  J=d+\lceil\log_2(C+1)\rceil+
      \lceil\log_2(d+1)\rceil.
\]

Then every reduced coefficient \(h_j\) of the exact rational polynomial
\(H(t+z)\), not merely the first few Taylor jets, satisfies

\[
 \boxed{
  \operatorname{bits}(\operatorname{num} h_j)
       \le n+m+\ell(E+J)+1,\qquad
  \operatorname{bits}(\operatorname{den} h_j)
       \le \ell E+1,
 }
\]

and \(\deg_z H(t+z)\le\ell d\). These are integer
ceilings depending polynomially on the **expanded rational replacement
input**, not necessarily on a succinct description of an auxiliary
construction. The canonical dense polynomial representation satisfies
\(K\le n\ell(d+1)\), so the bit bound is polynomial in
\(n,m,\ell,d,b\). However, a complete paper theorem must
**separately prove** that its implicitly generated coefficients
have polynomial degree and bit length in the original network/CNF
parameter and that producing the needed entries is total and
sufficiently cheap. No such conclusion is obtained merely from
this output lemma. The bound remains valid for \(\ell=0\), an
empty clause, contradictory clauses, and negative literals.

**Proof.** Write the center as \(t=p/q\) and take the global
positive common denominator

\[
  Q=q^d\prod_{\text{all }K\text{ coefficients }a} \operatorname{den}(a).
\]

Every shifted coefficient \(a_k\binom{k}{j}p^{k-j}/q^{k-j}\)
is integral after multiplication by \(Q\).
The coefficient's absolute numerator is at most
\(2^{E+d}\), because \(\binom{k}{j}\le2^d\)
and all remaining integer factors have total bit exponent at most
\(b(K+d)\). Every substituted Boolean literal sums at most
\(C=n(d+1)\) such terms; \((1-L)\) adds at most \(Q\).
Hence each false-literal coefficient times \(Q\) has absolute
value at most \((C+1)2^{E+d}\). Expanding the
outer product of \(m\) clause factors has at most \(2^m\)
selected products, each with at most \(\ell\) literal factors.
Every product coefficient has at most \((d+1)^\ell\)
selections. Finally sum over at most \(2^n\) Boolean
assignments. Thus each coefficient of \(Q^\ell H(t+z)\) has
absolute value at most \(2^{n+m+\ell(E+J)}\);
every output denominator divides \(Q^\ell\).
Reducing rational coefficients cannot enlarge either bit
length beyond these ceilings.

This is a polynomial bound on **information in the final answer**,
including its exact high-order Taylor coefficients. It is **not**
a bound on intermediate rational numerator growth, the cost of
producing/representing \(Q\), the number of tensor bonds,
the size of a factor table, measurement certification, oracle
work, retained memory or runtime totality. In particular, the
complete-bipartite CNF in the preceding section has a short
constant answer and still materializes exponentially many
dense table cells under the specified ordering.

**Executed independent validation:** GitHub workflow
\`42716567030\` passed 27 coefficient-bound tests and strict
typing (78 production source files plus the proof module).
The tests independently enumerate the full Boolean deformation
polynomial for signed, empty and contradictory CNFs, randomized
degree-two rational replacements and large rational inputs.
They verify the stronger common-denominator divisibility witness,
not only bit lengths. The actual small spectral projector
construction is tested at **every emitted interpolation center**,
without pretending it meets the literal manuscript schedule.

This closes the **final-output coefficient-height** sublemma
without closing any intermediate representation or source-totality
premise. The full paper theorem acceptance remains **RED**.

## Implicit spectral auxiliary coefficient heights

The source-specific extension in [eth-implicit-spectral-height.md](eth-implicit-spectral-height.md)
proves an independent, uniform rational-height bound for the **actual**
implicit Walsh kernel, every `row_at` polynomial and every restricted
exceptional projector entry. For parameters `r,Q,R` satisfying the
source input domain, queried row numerator/denominator bit lengths are
`O(Q log(Q+1) + R log(Q+1))`, independent of the virtual
matrix dimension `D=r**(2Q)`. The occurrence transfer adds only
`O(log(ell+1))` bits; its degree is at most `R-1`, and the
expanded replacement has at most `n*ell*R` rational coefficients.
The composed final-output bound can therefore be computed from the
original CNF dimensions and spectral parameters **without generating
that expanded replacement**.

This settles a separate bit-height obligation for the source's
implicit coefficient **values**, not its global construction cost.
The strict paper entrypoint still **defaults** to selector measurements,
with an explicit projected-basis opt-in established separately below.
Balancing work, projector numerical admission, all recursive children,
resource-cap non-refusal and large intermediate ranks still need independent
cost and totality proofs. The projected Gram/RREF work is separately bounded
for the *projector* route below. The complete theorem acceptance remains RED.

## Projected Gram and fraction-free basis bit bound

[The exact projected Gram reference](eth-projected-gram-bit-bound.md)
now proves a polynomial bound for the actual projected restricted
Gram/RREF stage. The implementation scales every exceptional
projector entry by `2**Q`, constructs an integer Gram matrix
over the occupied labels, and uses exact fraction-free Montante
elimination instead of `Fraction` Gaussian RREF. Each stored
intermediate is a signed matrix minor; determinantal bounds limit
its bit length to

```
k * (Q + 4 + 2*ceil_log2(ell+1) + ceil_log2(k+1)) + 4
```

for `k` active variables and at most `ell` occupied labels in
a copy. Symbolic cost and storage bounds include projector oracle
queries, exact integer pivots, Euclidean row normalization,
the projector cache, and retained primitive rows. Under the
paper's *conditional* balancing group-size inequality, at most
`Q*r*ell` such stages are invoked, each with
`k <= min(ceil(2*n/r), ell)`, so this stage has polynomial
bit-machine work and storage in the manuscript's admissible
numeric parameter regime.

The reference has an independently checked source correspondence
to the previous rational rowspace algorithm and preserves the
real projected measurement certificates. **This does not validate
the selector-mode strict paper constructor**, independent
balancing totality, the rest of the transfer, or the recursive
contraction's worst-case bit/memory recurrence. The complete
non-exponential theorem gate remains RED.

## Selector versus projected measurement row-space identity

The source-specific proof in
[eth-selector-projector-equivalence.md](eth-selector-projector-equivalence.md)
establishes the exact identity `G=B^T W B` for the restricted
exceptional selector matrix `B` and the projected Gram `G`,
with `W` positive definite. Consequently their rational row
spaces coincide, even for rank-deficient groups and collided
incidence labels. Exact source tests compare both original and
projected transferred representations, measurement witnesses,
center evaluations and final counts.

**Quantitative admission is not basis-invariant.** The row count,
primitive integer row `L1` norm, lambda coefficients and literal
measurement tuple domain can differ. The strict paper entrypoint
now provides an *explicit* `measurement_basis='projector'` opt-in
while preserving selector defaults; it still audits all original
parameter prerequisites and actual resulting `tau,D` bounds,
and it may refuse. This closes row-space equivalence, **not**
projected-mode numeric admission, full source-level construction
totality or the non-exponential recursive theorem. The theorem
acceptance remains RED.
