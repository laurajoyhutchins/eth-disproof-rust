# Independent formulations as reference oracles

The OpenAI Lean source is the authority for **source-faithful compilation**. Other ETH arguments can independently check the mathematics, but cannot certify an OpenAI instruction sequence merely by returning the same count.

## Pinned references

| Role | Source | What it can check |
| --- | --- | --- |
| Compiler source | [OpenAI Lean SAT and native counting development](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT), commit `4eaee87548250b2682affda7d05d947c05554bae` | Original declarations, physical graph, output, proof assumptions |
| Independent counting statement | [Anthropic `MainResults.lean`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/MainResults.lean), commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, blob `1c62a550fa1e4cbec65bb7112f92ad67589afddc` | Different CNF representation, independent satisfaction/count definition, expected output word, stated machine theorem |
| Independent proof | [Anthropic Lean formalization](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth) | Mathematical lemmas *after* their hypotheses and encoding have been related explicitly to ours |
| Alternative exposition | [Shiva Kintali, simplified ETH proof](https://shivakintali.github.io/papers/ETH.pdf); [Ryan O'Donnell's notes listed in the community review](https://mathcommunity.github.io/oai-math-revised/papers/The-Exponential-Time-Hypothesis-is-False-October-25-2026/) | Independent derivations and possible simpler witnesses; these are **not** source-execution oracles |
| Finite external experiment | [Community review: measurement-indexed counting](https://mathcommunity.github.io/oai-math-revised/papers/The-Exponential-Time-Hypothesis-is-False-October-25-2026/) | Additional small numerical results; source has heuristic parameters, so do not transfer its resource bound |

Pins above were retrieved November 15, 2026. Do not silently move the pins with upstream `main`.

## Representation boundary

The two Lean source models are not the same datatype.

- **OpenAI** uses `SAT.CNF (Fin n)`, a finite **set** of finite-set clauses; every literal is a zero-indexed variable and polarity. Our `Cnf::new` deduplicates literals and clauses. The original native machine takes its own nested unary/framed `Encoding.encodeCNF` bit word.
- **Anthropic** uses `CNF n = List (List (Fin n × Bool))`. Its theorem requires `IsKCNF k φ`: clause length at most `k`, with distinct *clause lists*. A clause list may repeat a literal and may contain both polarities. Different literal order makes a different list. `AllOccur`, `n ≥ 4`, `m ≥ 2` and `k ≥ 1` are additional hypotheses of `MainTheorem`.
- Anthropic's `encInput` starts with `1^k 0`, followed by `encClauses`: `1^n 0` then fixed-width, **least-significant-bit-first** positions. `slot none = 0`; for literal `(i,b)`, `slot = 2i + 1 + b.toNat`. Width is `Nat.log2 (2*n) + 1`. Its output is the lowest `n+1` bits of `numSat`, LSB first. This is **not** the OpenAI native input or output ABI.
- Both formula semantics interpret a clause as OR and a formula as AND. At the mathematical level, forgetting list order and duplicates preserves satisfaction for every Boolean assignment. This does **not** establish an equality of encoded words, runtime programs, transitions or complexity functions.

The first bridge is **proved** in [`IndependentCnfBridge.lean`](../rust/lean_eth_reference/proofs/IndependentCnfBridge.lean). The total conversion `IndependentETH.toCNF` preserves satisfaction and count for every Anthropic CNF, with no machine-theorem eligibility hypotheses. The count retains the `n`-variable universe, including unused variables. The original definitions are imported unchanged from their pinned revisions. In particular:

```text
IndependentETH.satisfiable_iff : MainResults.Satisfiable φ ↔ SAT.Satisfiable (toCNF φ)
IndependentETH.numSat_eq_count : MainResults.numSat φ = SAT.count (toCNF φ)
```

These are semantic identities, not statements about the two encoded inputs, executable programs, or time bounds.

## Acceptance levels

| Level | Evidence | What it establishes | What it does **not** establish |
| --- | --- | --- | --- |
| A. Finite external semantics | Source-pinned independent implementation of Anthropic's `Satisfiable`, `numSat`, `encInput`, `binary`; compare against OpenAI Rust's `Cnf` on bounded fixtures | OR/AND semantics, declared variables, polarity, multiplicity, output-word convention, and encoding expectations | Lean proof, asymptotics, or compiled-machine fidelity |
| B. Mathematical identity | Lean equivalence of the count models; separate checks of shared spectral/tensor identities against another derivation | Agreed mathematical counts and identities under stated assumptions | That Anthropic's algorithm is the OpenAI program |
| C. Original-source refinement | Original pinned OpenAI Lean run/physical trace compared with **generated** Rust, with original graph identity | Source execution correspondence on the checked domain | Universal theorem and machine resource bound |
| D. Resource refinement | Original primitive TM2 cost, intermediate coefficient bit lengths, and total recursion calls; independent asymptotic analysis | A bounded resource claim for a precisely identified machine/model | Practical speedup without end-to-end measurements |

The included Rust test `tests/anthropic_reference.rs` implements **only Level A** using the definitions in Anthropic `MainResults.lean`. It is intentionally independent of the crate's own `Cnf::eval` and `EnumeratingLeaf` when it produces expected counts. This finite oracle must never be called from the production counter.

## Where to compare the actual proofs

Anthropic's [proof-module map](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/README.md) identifies specific formal artifacts. These are **comparison candidates**, not established translations of our lemmas.

| Independent proof area | Our corresponding question | Next concrete check |
| --- | --- | --- |
| `sparsification/SparsificationLemma` and `threesat/Enumerate` | Does OpenAI's disjoint sparsification conserve exact assignments and respect declared variables? | Prove the same partition-of-assignments equality with an explicit translation of branches; track whether Anthropic's intermediate lemma proves decision or exact count |
| `networks/Groundwork`, `networks/Value`, `networks/Eight` | Are the network value, local replacement and group-routing equalities correct on finite concrete tensors? | Express each side as a finite sum on a common labelled graph; compare exact values and then prove the translation's hypotheses |
| `rates/GeneralPieces`, `rates/CountedRecursion`, `rates/ExplicitCost` | Is there a simpler independently stated recursion and total-operation bound that exposes our large-parameter bottlenecks? | Separate shared *mathematical* invariants from distinct packet/piece parameter schedules; record every coefficient bit cost and recursive call |
| `machines/ToTuring` and `machines/StepMachines` | How do finite-operation counts become primitive machine-step bounds? | Compare machine models and simulation hypotheses, not raw step counts or wall time |
| `variables/VariableBound` and `consequences/CountKSat` | Are the claimed counting bounds uniform over the input variables and clause width? | Check quantifier order and the no-duplicate/all-occur hypotheses independently of the central contraction |

Anthropic's proof map explicitly says some intermediate `threesat/` statements are **decision** forms even where the paper prints a **counting** theorem. Using such a statement as an exact-count oracle without checking its stronger companion would be a semantic error.

For each proposed shared lemma, the acceptance record needs (i) both source declarations and pins; (ii) a total conversion of the objects; (iii) hypotheses and precision assumptions; (iv) a Lean equivalence theorem or two genuinely independent calculations; (v) a counterexample when an essential hypothesis is removed. A resemblance between the two papers is not evidence of source equivalence.

## Verified source-level count bridge and local algebra check

The Lean file [`IndependentCnfBridge.lean`](../rust/lean_eth_reference/proofs/IndependentCnfBridge.lean) imports the original pinned OpenAI `SAT.lean` and Anthropic `MainResults.lean` without changing their bytes and proves:

```text
IndependentETH.satisfiable_iff :
  MainResults.Satisfiable φ ↔ OAI...SAT.Satisfiable (toCNF φ)

IndependentETH.numSat_eq_count :
  MainResults.numSat φ = OAI...SAT.count (toCNF φ)
```

The full theorem names are in the Lean file. This is **all finite formulas**, not merely Anthropic's narrower machine-theorem input domain. The exact-head Lean checkpoint [run #43727057523](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43727057523) passed with axioms `propext`, `Classical.choice`, `Quot.sound` for each theorem.

[`IndependentSwapIdentity.lean`](../rust/lean_eth_reference/proofs/IndependentSwapIdentity.lean) proves `SWAP = I - vvᵀ` over the integers in basis (00,01,10,11), for `v=(0,1,-1,0)`. This is the local `SWAP = I - 2·singlet` formula in Anthropic's pinned exposition. The independent [Rust test](../rust/lean_eth_reference/tests/independent_swap_identity.rs) also checks exact expansions and contracted integer values for 1–3 crossings.

### Arbitrary finite network contraction, grouped by weight

The same Lean module now contains `finite_contraction_grouped` and `finite_swap_contraction_grouped`. The former expands any finite product of local sums, then interchanges the finite contraction sum and mode sum, and groups modes by their number of correction factors. The latter instantiates it with the **signed** rank-one singlet correction at every swap crossing.

Its states are an arbitrary finite set of joint boundary assignments; an arbitrary integer coefficient may encode all other node tensors, incidence constraints and shared wires. Neither independence of crossings nor a fixed network size is assumed. The identity holds for zero crossings, repeated/shared boundary variables, and negative coefficients.

The proof uses `Finset.prod_add`, `Finset.sum_comm`, and `Finset.sum_powerset`. [Exact-head Lean workflow #43741399685](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43741399685) passed at commit `d757ce4` with only `propext`, `Classical.choice`, and `Quot.sound` for both new theorems. This is an **algebraic** theorem: expanding the powerset has `2^|E|` terms. Neither this grouping nor the local singlet identity establishes a fast algorithm, Anthropic's low-rank grouping bound, or correspondence with OpenAI's packet-mode routing.

Most importantly, the correction `-vvᵀ` has odd entries. Singlet Hamming weight is **not** automatically 2-adic valuation. Discarding high-weight terms modulo `2^p` requires a separate divisibility proof, stated for the actual OpenAI coefficients and routing.

## Group-routing and precision boundary (15 November 2026)

[IndependentRoutingBoundary.lean](../rust/lean_eth_reference/proofs/IndependentRoutingBoundary.lean) separates two mathematical operations:

1. **Route/factor:** After fixing a shared outer assignment, sum each independent group setting and multiply those group sums. The outer assignment's sum remains *outside* the product. A concrete two-setting counterexample shows that pulling it inside produces the wrong value.
2. **Truncate:** In a ring with `2^p = 0`, a mode of weight `w ≥ p` may be discarded **if its actual coefficient contains the factor `2^w`**. This is a divisibility certificate, not a consequence of its label.

The new `group_sum_product`, `conditional_group_contraction`, `two_power_vanishes_above_precision`, and `weighted_mode_cutoff` theorems passed [Lean #43755368182](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43755368182) at commit `4d290da`, with only `propext`, `Classical.choice`, and `Quot.sound` among their axioms.

### Exact pinned source landmarks

| Source | Declaration | What is actually proved | Missing comparison |
| --- | --- | --- | --- |
| [Anthropic Value/Sums.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Sums.lean) | `Value.stSumsInside` and `Value.stSumOut` | Color-group node settings form a bijective regrouping; edge-label sums recover the original pair interaction | Translate its concrete network and group settings to a common finite contraction |
| [OpenAI SubexpComputedWeights.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SubexpComputedWeights.lean) | `momentWeight_reconstruct`, `enumeration_weight_split` | Monomial weights split across **disjoint supports** after field-assignment reconstruction; the coordinate lift is arbitrary | Source-specific adapter for these field/moment objects; no identification with Anthropic singlet modes |
| [OpenAI scope](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/378.md) | `SqrtLogSpace.exact_count_and_sat` | Exact counting by a formal primitive machine at the stated **Lean** running-time bound | The sharper October 25 manuscript bound is a distinct claim; do not transfer it automatically |

The OpenAI `SubexpComputedWeights` development is part of a prime-field moment construction. It is **not** the separate appendix's 2-adic packet-mode truncation. The latter still requires extracting precise source definitions, normalizations and coefficients before a source-specific Lean bridge can be stated.

### Why direct mode matching is not the right goal

For the signed swap decomposition `SWAP = I - vvᵀ`, one correction entry is `-1`. Thus `2 ∤ -1`, even though the term has singlet Hamming weight one. Rewriting it as `-2·singlet` introduces a denominator in the projector; it does not grant integral 2-adic divisibility. Naively deleting every weight-one term modulo 2 changes the result.

The appropriate comparison diagram passes through a common *contraction value*:

```text
Anthropic network + exact group expansion
           │ source-specific value preservation
           ▼
       Finite contraction
           ▲
           │ source-specific value preservation + precision certificate
OpenAI packet network + weighted modes
```

The two expansions need not have bijective mode sets. Cancellation can occur between different terms. A proof must identify the same underlying finite network, the conversion of assignments and factor coefficients, and the ring/precision maps on each side. Only then can the resulting contraction values be equated or compared modulo a justified power of two.

This is not yet an algorithm-equivalence theorem: neither source-specific value-preserving conversion, nor the appendix's source-derived valuation certificate, is established. No improved resource bound follows from regrouping finite sums.

### Next acceptance obligations

- Define one finite labelled-network semantics with explicit original edges, ports, factor order and coefficient ring.
- Prove an **Anthropic adapter**, reusing its own `Value.stSumsInside` and `Value.stSumOut` where possible.
- Prove a separate **OpenAI adapter** for the exact intended algorithm. Do not substitute its prime-field body for the appendix's 2-adic packet program.
- Prove a divisibility/valuation lemma for every discarded mode from the *actual coefficient construction*; exercise weights `p-1` and `p`, odd entries, and noninvertible denominators.
- Test a deliberately wrong routing, a shared outer assignment, and a non-divisible singlet correction as negative controls.

## Required adversarial corpus

1. Empty clause (unsatisfiable), empty formula (all assignments), unused declared variables (factor of two per unused variable).
2. Positive/negative literal reversal, repeated literal within a clause, mixed-polarity tautology, duplicate clauses, permuted clauses and permuted literals.
3. A valid instance of Anthropic's `MainTheorem` hypotheses, including at least four variables, all occurring, at least two distinct clause lists; another instance violating each hypothesis to establish that finite semantic equality does not imply theorem applicability.
4. Wrong literal-slot polarity, 1-based versus 0-based indexing, LSB/MSB reversal, unary-prefix length, padding, overflow and truncation of the `n+1`-bit count.
5. At each *shared* algebraic lemma, sample exact integers and matrices, not floats; perturb valuation cutoffs `p-1` vs. `p`, signs, nonunit denominators, and group routing. This requires a separately proved correspondence for the lemma's objects, not similarity of terminology.

For an actual independent executable comparison, run the **original Anthropic machine** and the **original OpenAI machine** (or justified extractions) on equivalent inputs, check both counts and record their different encodings, toolchains and source hashes. If either machine is unavailable on an admitted input, report unsupported. Do not replace it with brute force and label it an independent machine run.

## Priority for our current work

1. **Complete:** Pinned source-level CNF meaning bridge, all formulas; local signed-swap identity; finite Rust oracle.
2. **Complete:** Exact-head Lean kernel verification of arbitrary finite signed network contractions, including Hamming-weight grouping; no extra axioms.
3. **Next mathematical bridge:** Construct a total, source-defined translation from Anthropic's grouped network objects to OpenAI's packet-mode objects; state a common contraction value and prove equality or a correctly justified `2^p` congruence. Keep Hamming weight and 2-adic precision distinct.
4. **Independently required:** Finish [OpenAI source-to-Rust acceptance](lean-rust-acceptance.md), including the nonterminal query/leaf/DFS/outer chain, noncomputable finite fallback refusal, exact original traces and primitive TM2 accounting.

A successful finite comparison is useful regression evidence. It is not a theorem acceptance receipt, a faithful ETH executable witness, or an ETH complexity benchmark.
