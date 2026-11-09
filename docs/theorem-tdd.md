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

The suite contains green checks of conditional recurrence algebra, failure-closed cost
accounting, fabricated-ledger refusal and opaque-oracle work, plus the deliberately **red**
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

Several source-loop costs now have conditional envelopes and are charged
in `reference/whole_frame_recurrence.py`, including packing, mode ordering,
catalog construction, child preparation, coefficient arithmetic and recovery.
Those envelopes are **not** a complete universal cost certificate: generated
oracle bit-work, source correspondence, capacity non-refusal and working-set
bit accounting still require independent proofs.

The acceptance now has three distinct gates, documented in
[complete-theorem-acceptance.md](complete-theorem-acceptance.md):
complete local bit work; source correspondence and totality; and, for Sudoku,
the asymptotic conversion to **cells**, not just network edges. The current
conditional frame bound `2^{O(s loglog(s)/(log s)^(1/4))}`, with direct
encoding `s=Theta(N log N)`, does **not** imply `2^{o(N)}`. This is a
limitation of the displayed upper bound, not a runtime lower bound.

## Advancement rule

Keep the red test in source control, visible and independently runnable.
Only mark it green after proving every required term, verifying the
correspondence of those proofs to the implementation, and establishing
non-refusal on the declared input family. Later tests must tackle the final
asymptotic limit separately. Do not silently substitute an exponential
exhaustive leaf for a missing proof.
