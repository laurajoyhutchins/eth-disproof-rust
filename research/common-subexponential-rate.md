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

### The original Cauchy grid: scalar normalization now kernel-checked

The pinned October 25 appendix fixes the grid `S={-L,…,L-1}`, `L=2^a`, `α=2^(a+1)=2L`. Its coefficient ring is `O=ℤ_(2)[U]/(f)`. The proof now works in that concrete two-local ring shape, rather than treating its integrality assertion as a premise.

| Source module under `eth/proofs/` | Kernel-checked result |
| --- | --- |
| `IndependentCauchySourceGrid.lean` | Literal source interval, exact root product and grid-index bijection `S ≃ Fin α ≃ ZMod α`, difference bound `|t-q|<α` and source derivative-product reindexing |
| `IndependentCauchyBinomialParity.lean` | Lucas parity: every `choose(2^m-1,k)` is odd for `k<2^m` |
| `IndependentCauchyFactorial.lean` | Source-specific derivative products `D(t)=(-1)^(n-k)k!(n-k)!`, `D(t)·choose(n,k)=(-1)^(n-k)n!` with `n=2L-1`, `k=t+L`; each binomial is a unit modulo `2^p` |
| `IndependentCauchyTwoLocal.lean` | Every nonzero source difference `t-q=2^v d` with `v≤a` and odd `d`; a constructive `w` with `(t-q)w=α`, first in `2^p=0` rings and then in every odd-local ring; `C(t+αz)=αD(t)N_t(z)` |
| `IndependentCauchyNormalization.lean` | Since the source binomial is odd, `D(t)=D(0)u_t` without cancellation of the generally nonunit `D(0)`; for every odd-local ring `R`, a polynomial `P_t∈R[X]` satisfies `C(t+αX)=αD(0)P_t(X)` |
| `IndependentCauchyLocalRing.lean` | Construct `ℤ_(2)` as localization at all odd integers and `O_f=ℤ_(2)[U]/(f)`; prove all odd integers become units and instantiate `C(t+αX)=αD(0)P_t(X)` in `O_f[X]` for every `f` |
| `IndependentCauchyFormalDerivative.lean` | Define the actual source polynomial as the nodal product; prove it agrees with `C` and that `eval₀ (derivative C)=D(0)` exactly |
| `IndependentCauchyTileMode.lean` | The normalized crossing-tile finite inverse, its uniqueness and degree-`b` factor `2^(b+1)` in a `2^p=0` ring |
| `IndependentPacketModeSelection.lean` | Fixed-mode-exponent aggregation retains `2^(Σ_Z w_Z β_Z)`, including all row selections, with heavy coefficients vanishing modulo `2^p` |

In particular, the source's fixed-denominator normalization is no longer merely a rational calculation:
```text
D(t) = ∏_{q∈S, q≠t} (t-q)
C(t+αX) = α·D(0)·P_t(X)     in O_f[X]
D(0) = (d/dT C(T))|_{T=0}  over ℤ.
```
The quotient polynomial is constructed by multiplying finite, explicitly integral factors. Its proof never cancels a nonunit denominator in `O_f`. The `O_f` theorem is valid for every polynomial `f`; the manuscript's additional monicity and mod-two irreducibility hypotheses are needed elsewhere, not for this scalar divisibility result.

**Remaining attachment to the original recursive algorithm.** The source defines the entrywise Cauchy weight `W_xy(T)=C(T)/(C'(0)(T-(y-x)))` in the fraction field. The just-proved scalar normalization does **not** by itself establish integrality of those punctured products after removing the `T-(y-x)` factor. Prove `W_xy(t+αX)∈O[X]` directly, including the cases `y-x=t` and `y-x≠t`, identify the resulting crossing-tile coefficients with the verified `IndependentCauchyTileMode` series, and construct the original `A_p` quotient and its coefficient maps.

Even after those links, the independent group-child contraction identity, restricted-partition enumeration and bit-operation/peak-space bounds remain separate. The verified scalar lemma is not a full ETH disproof or a cost-preserving OpenAI/Anthropic algorithm equivalence.

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
