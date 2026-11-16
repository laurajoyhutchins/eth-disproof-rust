# Common exact counting and subexponential rates

## The statement worth comparing

Let `k ≥ 2` be fixed. Let `φ : MainResults.CNF n` be eligible for Anthropic's original Main Theorem: `IsKCNF k φ`, at least two clauses, `n ≥ 4`, and every variable occurs. Put

```text
F := IndependentETH.toCNF φ : OAI.Algorithms.SubexponentialSAT.SAT.CNF (Fin n).
N := SAT.count F = MainResults.numSat φ.
```

The unchanged pinned original definitions, imported together in `IndependentCnfBridge.lean`, prove both equality of counts and `SAT.WidthAtMost k F`. **Therefore both independently proved source-level machine theorems apply to the same mathematical input**. They do not take the same encoded word.

The two theorems are:

| Source theorem | Model and input | Output | Time |
| --- | --- | --- | --- |
| OpenAI `SqrtLogSpace.exact_count_and_sat` at `openai/math@4eaee875`, `SqrtLogSpace/Final.lean` | One primitive multi-tape machine for fixed `k`, input `Encoding.encodeCNF F` | `countWord (SAT.count F)`; also SAT bit | `C_k (L_O+1)^{d_k} 2^{A_k n (ln ln(n+16))²/√ln(n+16)}`; polynomial all-prefix visited space |
| Anthropic `MainResults.mainTheorem` at `anthropics/formal-math@16a5ce4`, `Solution.lean` | One finite-alphabet TM2 machine and a constant `C` uniform across `k`, input `MainResults.encInput k φ` | `MainResults.binary n (numSat φ)` | `2^{C min\{k m/√log₂m, k² n log₂log₂n/√log₂n\}}`, rounded down |

The OpenAI expression is the **proved Lean scope**, not the sharper October 25 manuscript expression. `L_O` is the actual OpenAI encoded length, and `m=φ.length`. The Anthropic machine theorem is stated for `k≥1` but the shared domain uses `k≥2` for OpenAI.

## Machine-level Lean corollary

`IndependentETH.original_anthropic_machine_counts_openai_with_rate` is a theorem in the current repository. It takes a proof `hMain : MainResults.MainTheorem`, retains the **same original Anthropic TM2 machine**, the same Anthropic input word and the same `timeMin`, but replaces the output count in its conclusion by **OpenAI's actual `SAT.count (toCNF φ)`**. This is justified by the separate, proved `numSat_eq_count`. No cost assumption for the representation conversion is used inside this theorem: the underlying machine is still run on its original native encoded input.

`MainResults.mainTheorem : MainResults.MainTheorem` is proved at the pinned Anthropic source in `eth/Solution.lean`. The small cross-source file imports its exact **statement** and accepts a term of that proposition. It does **not** import the hundreds of source proof modules or falsely claim an unconditional proof of that source theorem in the cross-source Lean environment.

OpenAI's pinned `SqrtLogSpace.exact_count_and_sat` independently proves a primitive-machine count with the `runtimeBound` above for every `SAT.WidthAtMost k F`. The new `toCNF_width_at_most` supplies exactly that admission premise. The two source-machine witnesses count `N`, with two different inputs, outputs and precise time bounds.

## Why both times are subexponential

For each fixed `k`, `n→∞` gives

```text
(ln ln(n+16))²/√ln(n+16) → 0,
(log₂ log₂ n)/√log₂ n → 0.
```

The `IsKCNF` condition on distinct ordered clauses of length at most `k` bounds `m ≤ (2n+1)^k` and makes **both native encoded input lengths polynomial in `n` for fixed `k`**. Hence the fixed-degree polynomial factor in OpenAI's machine bound is `2^{o(n)}` too. This establishes a **shared mathematical 2^{o(n)} classification** of the two *native* counting results. It does not establish equal run times or improve OpenAI's squared `log log n` numerator. The required logarithmic limits are standard calculus consequences; this repository does not yet have one combined Lean theorem importing both source final theorems and formalizing all of those asymptotic steps.

## Why the earlier packet correspondence does not prove a rate

The direct two-node packet-to-Anthropic-network conversion labels its shared edge by an entire `M`-bit column assignment. At `W=I`, the resulting interaction matrix is `I_{2^M}`, so its matrix rank is `2^M`. **Any factorization across that fixed two-node cut uses at least `2^M` labels** over a field. Even though the conversion preserves every integer contraction exactly, it cannot be used as a low-cost subexponential simulation.

Subexponential equality of results is established *by independent native machine theorems plus the counting conversion*, not by this exponential interface. A stronger claim that OpenAI's **original packet factors themselves** implement Anthropic's specific small-rank crossing decomposition remains unproved and may not be true. To claim an efficient inter-algorithm reduction, it is necessary to provide an alternate decomposition or a streaming machine-level translation with a subexponential **total** operation bound.

## Acceptance frontier

1. **Proved in cross-source Lean:** literal, clause and CNF satisfaction/count correspondence; `IsKCNF ⇒ WidthAtMost`; the Anthropic time-bounded native machine theorem reformulated to output OpenAI's count, *conditional on the original Anthropic MainTheorem proof term*.
2. **Proved separately in original Lean sources:** OpenAI's complete primitive-machine counting and its rate/space bound; Anthropic's complete TM2 counting theorem and its time bound.
3. **Still open as a single mechanically checked composite:** import both final source proof terms in a compatible Lean environment, prove the native input length bounds and logarithmic asymptotics there, and typecheck one joint theorem. This is much stronger than testing matching outputs, but does not demand a false factorwise identification.
4. **Still open for algorithm equivalence:** a cost-preserving translation of actual intermediate packet/piece factors and execution traces. Neither the verified CNF bridge nor the complete native-machine endpoint theorems entails this.

The relevant source pins and exact module names are in [independent formulations](independent-formulations.md). The cost study is [two-adic recursion](two-adic-recursion.md).
