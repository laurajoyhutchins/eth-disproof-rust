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
3. **Sudoku-cell parameter:** a bound `log2 T(s) = O(s (loglog s)^beta / (log s)^alpha)` and an encoding using `s=Theta(N (log N)^delta)` transfer to `log2 T(N)=o(N)` from this upper bound only when `alpha>delta` or `alpha=delta` and `beta<0`. The implemented source's current conditional parameters are `alpha=1/4, beta=1`, whereas the direct Sudoku encoding has `delta=1`. Consequently the *displayed upper bound* is too weak to establish subexponential behavior in the number `N` of Sudoku cells.

The last conclusion is about the available **proof bound**, not a lower bound on the solver. An algorithm might be faster than a loose upper bound suggests. For the explicit growing box-order family `b=2**k`, one has `N=2**(4k)`, `M=6kN`, and `lambda=ceil(log2 M)<=10k`. Hence

\[
\left(\frac{M}{N\lambda^{1/4}}\right)^4
=\frac{(6k)^4}{\lambda}\ge\frac{648}{5}k^3\longrightarrow\infty.
\]

The iterated logarithm multiplier in the current bound makes the transfer even weaker. A proof of `2**o(s)` measured in Boolean network edges does not by itself discharge the stronger `2**o(N)` cell claim for this reduction.

`CompleteTheoremStatus.require_complete()` reports *all current blockers* instead of raising only on the first missing local term. It obtains the source/totality blockers from the composed recurrence's `OPEN_PREMISES` and the cell-transfer gap from the actual published rate and reduction. There is no caller-supplied boolean that makes these obligations vanish. This is an engineering guard, **not** a formal proof checker: future positive results must update the independent mathematical source proofs, their implemented correspondence, and the gate together.

The single complete-theorem test remains **unskipped and un-xfailed**, outside ordinary checkpoint CI. It cannot be marked green merely by filling local cost fields. A non-refusing worst-case theorem, its bit-operation recurrence, and its claimed input-size parameter must be established independently.


## A total exact baseline that does not prove the target theorem

\`reference/total_exact_cnf.py\` provides a separate, **total mathematical
reference kernel** for exact #SAT on already-normalized \`CNFFormula\`
inputs. It performs ordinary, fixed-variable-order dense factor
elimination using nonnegative integer counts. There are **no configured
capacity refusals** or conditional unproved black-box oracles in the
algorithm. On finite hardware an enormous table can still exhaust
memory; mathematical totality does not mean physically runnable for
arbitrarily large inputs.

This makes one complete, explicit bit-machine complexity upper bound
available as a control. It is not a bound for the paper's algorithm.

For an input with \`n\` Boolean variables, \`m\` normalized clauses,
and maximum clause width \`w<=n\`, define

\[
B=n+\lceil\log_2(m+n+3)\rceil+
\lceil\log_2(w+2)\rceil+8.
\]

The symbolic envelope \`total_reference_envelope(n,m,w)\` reports
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
therefore in \`[0,2**n]\` and uses at most \`n+1\` bits. At most
\`m+n+1\` factor tables and one output scratch table coexist, each
with at most \`2**n\` Boolean assignments. Clause construction has
at most \`m*2**n*w\` literal tests. Across \`n\` elimination rounds,
there are at most \`2**n\` assignments per round, no more than
\`m+n\` attached factors and at most \`n\` bit extractions per
factor index. Deterministic scope scans and all dense table
allocations have polynomial overhead. The explicit constants
cover these scans and the listed abstract word operations after
their expansion to schoolbook bit steps on \`B\`-bit operands.

The kernel records actual additions, multiplications, operand-aware
schoolbook charges, modeled scope/mask events, peak simultaneous
table entries and model bit cells. It checks its observed execution
against its independently computed symbolic envelopes. It does not
pretend those counters enumerate the native Python interpreter,
object allocation, DIMACS parsing, or the cost of normalizing an
arbitrary unvalidated CNF into the \`CNFFormula\` ABI. The proof
applies to the specified abstract dense-array algorithm; the
source is an executable reference implementation of that algorithm.

The tests compare exact counts with independent exhaustive enumeration
on adversarial small CNFs, including zero variables, empty clauses,
unconstrained declared variables, contradictions, signed literals,
dense interactions, and randomized formulas. They also compare this
total reference with the existing *capacity-limited* fused ETH
evaluator on an identity deformation. A real subcubic Sudoku
encoding can be fed into the symbolic envelope without running
its astronomical \`2**n\` computation.

**The exponent is still linear in n**. This reference therefore
provides a complete **exponential** bit upper bound, not a
non-exponential worst-case algorithm, no universal result for
arbitrary vertex-oracle networks, and no \`2**o(N)\` Sudoku theorem.
In particular, it cannot be substituted as the missing
\`LocalBitBound\` of the paper schedule. The existing
\`research_acceptance/test_complete_bit_recurrence.py\` stays RED
and \`OPEN_PREMISES\` stays unchanged.

This isolates a precise research obligation: replacing the
\`2**n\` dense-table/assignment factor by a proved smaller total
representation in the admitted paper regime, without merely moving
its cost into coefficient bit lengths, a refusal cap, an oracle, or
the Sudoku-to-network parameter conversion.

Run:

\`\`\`bash
PYTHONPATH=src:. python -m pytest -q tests/unit/test_total_exact_cnf.py
python -m mypy --strict reference/total_exact_cnf.py
\`\`\`
