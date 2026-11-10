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

Existing acceptance remains intentionally **RED**. No independent
theorem registry, scheduler or additional CI workflow is needed.

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
The current strict paper entrypoint still uses selector measurements;
balancing work, selector/projector cutover, all recursive children,
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
