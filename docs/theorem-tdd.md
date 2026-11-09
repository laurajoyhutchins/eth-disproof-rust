# TDD for a complete worst-case bit-operation recurrence

**Research claim: unresolved.** The existing `reference/recurrence_calls.py` bounds
recursive *invocations*, not bit operations. The existing `reference/bit_work.py`
bounds selected outer loops, conditional on the cost of opaque ring operations
and vertex oracles. Neither proves that a generalized Sudoku instance completes
without a capacity refusal.

Run the explicitly opt-in research acceptance suite:

```bash
PYTHONPATH=src:. python -m pytest -q research_acceptance/test_complete_bit_recurrence.py
```

The suite contains four green checks of conditional recurrence algebra and
failure-closed cost accounting and an opaque-oracle counterexample, plus the intentionally **red**
`test_complete_bit_recurrence_for_current_paper_solver`. The research test
lives outside the default `tests/` discovery path and all checkpoint,
integration and extended gates. It has **no xfail or skip**.

## The mathematical condition

For each actual recursive frame, including generated packet-entry oracles,
prove a *uniform bit-operation* local bound `U_d`. With actual child bound
`K_d`, prove by induction:

\[
T_d \le U_d + K_d T_{d+1}.
\]

The executable `unfold_conditional_bit_recurrence` only verifies the
**conditional recurrence arithmetic**; it does not validate numerical upper
bounds as mathematical facts. `LocalBitBound` rejects omitted or negative terms.
A dictionary of made-up positive integers is *not* a proof, as its tests
explicitly demonstrate. Each term needs an independent universal lemma or a
machine-checked certificate before `current_local_bit_evidence` can contain
it. Time measurements, event-ledger counters, and branch caps are not valid
substitutes for bit-cost lemmas.

The first actionable gap is **recursive packet-entry-oracle closure**: a
newly generated oracle needs a bounded description size, cost of evaluation,
and coefficient precision, recursively, for every admitted child. Other
open terms include packing, factor elimination, exact rational recovery,
modulus construction, and terminal work with no capacity refusal.

Closing the local recurrence still would **not** prove `2^{o(N)}` for `N`
Sudoku cells. The direct encoding has `M=Theta(N log N)` Boolean edges and
`2^{O(M/sqrt(log M))}` alone only gives `2^{O(N sqrt(log N))}` in the cell
parameter. Exactness, unconditional completion, the complete recurrence, and
the final asymptotic conversion are separate acceptance obligations.

## Advancement rule

Keep the red test in source control, visible and independently runnable.
Only mark it green after proving every required term, verifying the
correspondence of those proofs to the implementation, and establishing
non-refusal on the declared input family. Later tests must tackle the final
asymptotic limit separately. Do not silently substitute an exponential
exhaustive leaf for a missing proof.
