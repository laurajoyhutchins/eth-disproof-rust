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

## Original OpenAI packet appendix: the separate source-rate obligation

The proven OpenAI source machine `SqrtLogSpace.exact_count_and_sat` is **not** a Lean proof that the October 25 Cauchy packet recursion is implemented or admits Anthropic's factorization. The packet paper's source [`quantitative-contraction.tex`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex), especially lines 384–600, makes the following separate quantitative chain:

1. The actual geometric row expansion (not the signed singlet expansion) must establish that every weight-`b+1` mode coefficient has a factor `2^{b+1}`, so modes of total weight at least `p_t` vanish.
2. The surviving mode exponents have source bound `exp(O_C(s/√λ * (√2/8)^d))` at recursion depth `d`, with `λ=ceil(log₂s)`. This uses `M≤Cs·8^{-d}`, `u_d=Θ_C(λ·2^{-d})`, and the source's packing hypotheses.
3. The source upper bound on the total number of calls is `exp(O_C(s/√λ)+O_C(λ log λ)) = exp(O_C(s/√λ))`; leaves cost `2^H` with `H≈s/√λ`, and implicit packet-entry evaluations cost `exp(O(s^{9/10}))`.
4. The interpolation, canonical lifts, coefficient bit lengths, graph descriptions, and depth-first space costs must fit within the same total bound.

The new Lean lemma `IndependentETH.PacketSourceRate.source_depth_exponent_bound` checks **one actual numerical implication** in item 3 without assuming a fixed depth: with `q=√2/8≤1/4`, for all real `A≥0` and `D`,

```text
Σ_{d<D} A*q^d ≤ 4A/3.
```

It discharges the summation of the per-depth exponent **if** the source-specific per-level budget has been proved. It does not discharge the cost of each node. No original-packet end-to-end time theorem or runtime implementation is claimed.

### The original Cauchy grid and its normalization boundary

The actual grid is `S = {-L, …, L-1}` where `L = 2^a` and `α = 2^(a+1) = 2L`. New Lean files now distinguish the parts that have been checked from the parts still needed:

| File | Kernel-checked result | Missing source attachment |
| --- | --- | --- |
| `IndependentCauchySourceGrid.lean` | Literal source interval; `|t-q|<α` for grid points; exact factorization `C(t+αz)=αz·∏_{q≠t}(t-q+αz)`; explicit nonzero `C'(0)` product; `S ≃ Fin α ≃ ZMod α`; center-independent divisibility counts for residues | Prove that casting the actual integer differences to `ZMod α` preserves each two-adic valuation and establish the derivative factorial formula |
| `IndependentCauchyBinomialParity.lean` | For every `m` and `k<2^m`, `((2^m-1).choose k)%2=1`, by the imported Mathlib Lucas congruence | Connect this parity to the factorials of the actual derivative products |
| `IndependentCauchyTileMode.lean` | Exact finite geometric inverse, reconstruction, uniqueness and `2^(b+1)` coefficient divisibility for a normalized unit denominator; odd denominators are constructively invertible in a ring with `2^p=0` | Identify the normalized numerator and denominator with the literal `W_xy(T)` inside `A_p` |
| `IndependentPacketModeSelection.lean` | A fixed mode-exponent coefficient retains `2^(Σ_Z w_Z β_Z)`, and heavy coefficients vanish | Identify source row-polynomial coefficients with those selected-mode sums |

There is a direct factorial reduction of the missing Cauchy normalization. Put `n=2L-1` and `k=t+L`, with `0≤k≤n`. The integer product at a source grid point has the mathematical identity

```text
D(t) := ∏_{q∈S, q≠t} (t-q) = (-1)^(n-k) · k! · (n-k)!
D(t)/D(0) = (-1)^|t| · choose(n,L)/choose(n,k).
```

The parity theorem verifies the oddness of both binomial coefficients on the right (because `n=2^(a+1)-1`). Their ratio is therefore a unit in `ℤ_(2)`. For every distinct pair `t,q∈S`, the checked bound `0<|t-q|<α` implies that `α/(t-q)` is two-locally integral. Consequently, over the fraction field the normalized numerator has the exact factorization

```text
C(t+αz) / (α C'(0))
  = z · [D(t)/D(0)] · ∏_{q∈S, q≠t} (1 + αz/(t-q)).
```

Every displayed factor is then two-locally integral. This is a **mathematical derivation** of the source's scalar-integrality claim, not yet a single Lean theorem: the factorial identities, integer-to-residue valuation transfer, and construction of the `ℤ_(2)` and `A_p` embeddings remain to be formalized and joined. In particular, do not replace this with the weaker fact that a generic finite mode series can be truncated.

Once that literal `W_xy` bridge exists, the original packet-to-child coefficient identity and per-node work bound are still separate obligations. Completing scalar integrality alone is not a proof of the source's subexponential algorithm.

The equality through a `2^M`-label Anthropic network is **disqualified as a cost-preserving bridge**. To prove the *same overall subexponential result via packet-to-piece correspondence*, one must construct a replacement with `2^{o(s)}` **total work**, formally bound its table creation and label enumeration (not just its final rank), and prove its recursive contraction identity in the actual coefficient ring. Showing independently that two different original native machines each run in `2^{o(n)}` is valid, but does not establish this stronger algorithm-to-algorithm statement.

## Why the earlier packet correspondence does not prove a rate

The direct two-node packet-to-Anthropic-network conversion labels its shared edge by an entire `M`-bit column assignment. At `W=I`, the resulting interaction matrix is `I_{2^M}`, so its matrix rank is `2^M`. **Any factorization across that fixed two-node cut uses at least `2^M` labels** over a field. Even though the conversion preserves every integer contraction exactly, it cannot be used as a low-cost subexponential simulation.

Subexponential equality of results is established *by independent native machine theorems plus the counting conversion*, not by this exponential interface. A stronger claim that OpenAI's **original packet factors themselves** implement Anthropic's specific small-rank crossing decomposition remains unproved and may not be true. To claim an efficient inter-algorithm reduction, it is necessary to provide an alternate decomposition or a streaming machine-level translation with a subexponential **total** operation bound.

## Acceptance frontier

1. **Proved in cross-source Lean:** literal, clause and CNF satisfaction/count correspondence; `IsKCNF ⇒ WidthAtMost`; the Anthropic time-bounded native machine theorem reformulated to output OpenAI's count, *conditional on the original Anthropic MainTheorem proof term*. A proposed reverse executable finite-set-to-list serializer was withdrawn after its typeclass/ordering proof did not compile; do not treat it as a verified machine preprocessor.
2. **Proved separately in original Lean sources:** OpenAI's complete primitive-machine counting and its rate/space bound; Anthropic's complete TM2 counting theorem and its time bound.
3. **Still open as a single mechanically checked composite:** import both final source proof terms in a compatible Lean environment, prove the native input length bounds and logarithmic asymptotics there, and typecheck one joint theorem. This is much stronger than testing matching outputs, but does not demand a false factorwise identification.
4. **Still open for algorithm equivalence:** a cost-preserving translation of actual intermediate packet/piece factors and execution traces. Neither the verified CNF bridge nor the complete native-machine endpoint theorems entails this.

The relevant source pins and exact module names are in [independent formulations](independent-formulations.md). The cost study is [two-adic recursion](two-adic-recursion.md).
