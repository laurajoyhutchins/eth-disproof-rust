# A local packet-entry work lemma (one proof obligation, not the theorem)

**Scope:** one already-prepared `PacketEntry._evaluate_python` call with
an eager, finite `Padic` or `JetRing` as its working coefficient ring.
It does not cover lazy expression-DAG or native Cython packet kernels, any
preparation or cache activity, embedding into a caller's ring, arbitrary
inherited parent oracles, or the bit complexity of coefficient operations.
The checker rejects native or non-eager working rings rather than giving
those paths a spurious bound.

## Coefficient-table invariant

For `k` target modes with nonnegative multiplicities
`beta=(beta_1,...,beta_k)`, every dictionary key created by the packet's
coefficient update is a length-`k` exponent vector `a` with
`0 <= a_i <= beta_i`. Initially all exponents are zero. The constant
transition preserves the vector; a contribution to mode `i` increments
only `a_i` and is taken only when `a_i < beta_i`. This proves the invariant
by induction on the processed rows. In particular, at **every** step the
number of keys is bounded by

\[
 S(\beta)=\prod_{i=1}^{k}(\beta_i+1).
\]

Let `r` be the number of rows, `d_j` the number of right-position terms
for row `j`, and `c_j` its number of target contributions. Let `T` be the
multiset of source tiles, of lengths `\ell_t`. The eager Python evaluator
makes **at most**

| Ring call | With target modes | With no target modes |
| --- | ---: | ---: |
| `add` | `sum(d_j)+S*sum(1+c_j)+sum(ell_t)` | `sum(d_j)+sum(ell_t)` |
| `sub` | `r` | `r` |
| `neg` | `sum(c_j)` | `0` |
| `mul` | `S*sum(1+c_j)+len(T)` | `r+len(T)` |
| `scalar` | `sum(ell_t)` | `sum(ell_t)` |
| `pow` | `len(T)` | `len(T)` |

The operations above are **outer calls**, not bit operations. `pow` can
perform many inner multiplications; source tile construction evaluates
Python integers `j**mode.b`, and dictionary key allocation/hashing is
not counted. Coefficient preparation already computed the Cauchy weights
and all cross-mode coefficients. A symbolic `S` may be enormous; the audit
does not materialize its states.

A canonical Padic value has `e*p` mathematical coefficient payload bits.
For nested jets of lengths `q_1,...,q_h`, the payload bound becomes
`e*p*product(q_i)` per stored coefficient value. These are bounds on
canonical *value payloads*, **not** process RSS, native object storage,
or intermediate arithmetic allocations. The checker also exposes the
number of prepared coefficient slots (`len(cauchy)+sum(len(contributions))`),
the corresponding payload-bit bound, and the maximum bit width of the
source `j**mode.b` values. Shared coefficient references are counted as
slots; Python object ownership is not inferred from this count.

The prepared local descriptor is finite and can be represented using
`O(L**2 + L*k + L*k_source)` integer/index entries for a packet of `L`
slots, `k` target modes and `k_source` source modes, plus the prepared
coefficient slots. This only bounds **one descriptor layer**: mode
metadata, parent geometry references and recursively inherited packet
oracles must be charged to their respective construction stages. It is
not a bound on the transitive closure of their Python object graph.

## Tests and negative witness

`reference/packet_oracle_work.py` computes these bounds using integers,
without enumerating the coefficient table. The checkpoint test
`tests/unit/test_packet_oracle_work_envelope.py` instruments the actual
`_evaluate_python` routine on real prepared child packet oracles and verifies
that every ring operation falls within the derived bound, at two precisions
and with and without a nested jet layer.

A separate synthetic local-update descriptor with `k` independent target
modes, all `beta_i=1`, achieves **exactly** `2**(k+1)-2` ring
multiplications over `k` rows. This witnesses that the generic table
implementation can incur exponential work in `k`. It is **not** evidence
that a paper-admitted recursive Sudoku child can realize that shape.
Eliminating this possible factor requires a structural reachability lemma,
a subexponential bound on the relevant multiplicities, or a different
representation/algorithm. Benchmarks cannot replace that obligation.

## Still missing for a universal recursive oracle-cost theorem

1. Bound creation work for `EvaluationContext`, Cauchy weights,
   `prepare_packet_terms` and the mode catalog, including integer powers.
2. Bound mode reachability and `S(beta)` under **the actual paper schedule**
   for every generated child, not merely an arbitrary prepared descriptor.
3. Close the bit costs of all finite ring and nested-jet operations, including
   precision changes and coefficient growth during rational recovery.
4. Bound the *transitive*, shared description size and evaluation cost of
   inherited packet oracles across successive recursive generations.
5. Include the work of the native or lazy implementation when selected.
6. Establish totality and the final input-size asymptotic limit separately.

Therefore `current_local_bit_evidence` remains empty and the research
acceptance test `test_complete_bit_recurrence_for_current_paper_solver`
**remains red**. This note proves a conditional local loop bound, not the
missing `U_d` theorem.
