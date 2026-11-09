# Center-evaluation work: conditional factor-elimination envelope

**Claim proved only for the enumerated outer loops of the Python factor
eliminator.** The new allocation-free helper is
`reference/center_evaluation_work.py`; the implementation checks are
`tests/unit/test_center_evaluation_work.py`. This is a TDD increment toward
`research_acceptance/test_complete_bit_recurrence.py`, which **remains red**.

It does not establish correctness on unbounded instances, non-refusal,
CPython/native bit complexity, or a subexponential Sudoku *cell-count* theorem.

## 1. Exact work requested by one paper center

Take a paper-active graph with `M` edges, `V` vertices and `P` packets,
slot width `L=2**a`, active coordinates `u`, current precision `p`, and
center `t` of valuation `i=v2(t)<u`. Assume the literal paper schedule
`a>=2u`, the packing invariant `P*L<=3M`, and all other mathematical
premises of the paper recursion. Then the implementation requests

\[
 h=\lceil3M/u\rceil,\qquad
 p_i=p+8hL/2^i+8M(a+1),\qquad
 E=M(2L-1)+1
\]

**deformation evaluations per center** under interpolation. This is an
*exact* count of requested samples, not a count of completed successful
contractions. The center `t=-L` is not evaluated because its Taylor order
is zero under `a>=2u`. The lemma does not apply to the experimental jet
recovery schedule.

## 2. How many actual child contractions can factor construction request?

`mode_catalog` creates at most one mode for every `(packet, y0, weight)`.
At a center of valuation `i`, there are `2**(i+1)` potential `y0` values
per packet. Hence at most

\[
 K_i=P\,2^{i+1},\qquad m_i\le K_i(p_i-1)
\]

mode variables/colors per weight and total mode variables, respectively.
Each admissible assignment (including every *partial* factor assignment)
obeys the same positive budget `sum_m weight_m*beta_m < p_i`. By the
existing colored-partition lemma in `global-mode-support.md`, the entire
admissible assignment domain has size

\[
 A_i\le 2^{\alpha_i},\qquad
 \alpha_i=4\lceil\sqrt{K_i p_i}\rceil.
\]

The factorization planner retains either one factor per occupied group or
one per connected component of the child incidence graph. A component
contains a retained parent vertex or a nonempty packet; no more than
`V+P` such objects exist, and the unsplit case adds at most one factor
per group. Thus, for paper `r=64` groups,

\[
 F_i\le64(V+P+1).
\]

`FactorBuilder.build` asks for **one child contraction per admissible
assignment of each factor scope**. Each scope domain embeds into the full
admissible domain by setting other variables to zero. Therefore

\[
 \boxed{\text{child contractions at one deformation sample}
          \le F_i A_i},\qquad
 \boxed{\text{child contractions at one center}\le E F_i A_i}.
\]

Caching, a zero factor, truncated child results and resource refusal can
only lower these counts; they cannot establish an exact answer. Distinct
factor assignments may invoke children with identical topology but
**different coefficient values**, so treating topology-cache hits as free
contractions would be incorrect.

## 3. Projected factor joins and coefficient work

Every factor table has at most `A_i` rows. Every row contains a truncated
formal generating polynomial with at most `p_i` nonzero degrees. The Python
sparse join examines no more than `A_i**2` pairs per factor join; an
elimination makes at most `F_i` such joins, and there are at most `m_i`
eliminations. Hence the number of pair checks is bounded by

\[
 \boxed{m_i F_i A_i^2}.
\]

Each sparse polynomial convolution examines at most `p_i**2` coefficient
pairs. The alternate `enumerate` path processes at most `A_i` projected
assignments, at most `p_i` values for its eliminated variable and at most
`F_i` incident factors. Consequently a deliberately loose bound on the
**outer** coefficient-ring calls in either Python path, including final
factor polynomial multiplication, is

\[
 64(m_i+1)(F_i+1)(p_i+1)^3(A_i+1)^2.
\]

The helper stores **ceilings of base-two logarithms** rather than
constructing the symbolic `2**alpha_i` table. It also separately gives the
`O(E**2)` outer ring-call envelope for Newton interpolation; each `inv`
requires its own previously modeled `Padic` inverse cost. The bound covers
ring calls, **not** their bit cost, factor ordering's arbitrary-precision
integer arithmetic, `FactorBuilder`'s degree-count preflight, Python
hashing/allocations or cache bookkeeping. Those steps are polynomial in
the displayed mode, factor, precision and *table-support* parameters in
the reference Python algorithms, but complete operation-by-operation
accounting and machine-level correspondence remain independent work.

## 4. What is asymptotic, and what is not

For successful paper paths with `M_0<=s`, `p_0<=s` and the uniform
packing/shrinkage/precision hypotheses, `global-mode-support.md` derives

\[
 K_i p_i\le B_\lambda s^2,\qquad B_\lambda\to0,
 \quad\lambda=\lceil\log_2 s\rceil.
\]

It further supplies an explicit expression for `B_lambda`. Splitting
recursion depths at `floor(log2(lambda)/2)` gives the conservative rate
`B_lambda=O(lambda**(-1/2))`: the shallow half has `u=Omega(sqrt(lambda))`,
while in the deep half `M_d/s<=(3/32)**d` decays faster than `1/lambda`.
Therefore `alpha_i=O(s/lambda**(1/4))`, uniformly across active depths.
The factors `F_i`, `m_i`, number of samples `E`, coefficient precision,
and ring-operation bit costs are polynomial in `s` under those premises.
Even multiplying `2**(O(alpha_i))` work across `O(log(lambda))` active
depths gives an exponent `O(s*log(lambda)/lambda**(1/4))=o(s)`.

**But this remains conditional**: we have not supplied an independent
bit-cost bound for *all* center setup, child packet coefficient preparation,
recursive child construction and inherited-oracle descriptions, nor replaced
finite resource refusals with a total algorithm. The native sparse kernel,
lazy coefficient DAG and paper mode *enumeration* path are not covered by
the Python factor-algorithm correspondence. A full worst-case recurrence
must charge these operations and the terminal leaf, then prove the
algorithm returns a count rather than a refusal.

At the **first** paper-active parameter, `u=1` and a loose finite upper
bound may exceed `2**s`. `2**o(s)` is a limit statement, **not** a
claim of subexponential improvement at every finite `s`. The tests
intentionally do not assert such a finite-size inequality.

Finally, `s=Theta(N log N)` for the current direct generalized-Sudoku
encoding in `N` cells. Even a proved `2**o(s)` Boolean-network bound does
**not** automatically give `2**o(N)` in cells.

## 5. TDD evidence and scope

- Small weighted-mode examples use an independent Cartesian-product
  enumerator for exact expected assignment counts.
- The real Python `ModeEliminator` is exercised in both `sparse` and
  `enumerate` modes, with native fallback disabled. Child-evaluation
  counts, factor retention and recorded ring calls stay within the
  independently derived envelopes.
- Formula tests verify the actual paper center precision and sampling
  definitions, including the essential center-by-center precision taper.
- A symbolic-size test checks the first active paper schedule without
  constructing a packet, field extension, or factor table. It intentionally
  makes no finite claim that the bound's exponent is smaller than `s`.
- Invalid paper premises are rejected, not silently treated as zero work.

The next proof obligations are **center setup/packet coefficient preparation
and child-description construction bit cost**, followed by a total leaf policy
and final recurrence composition. Do not mark the global theorem test green.
