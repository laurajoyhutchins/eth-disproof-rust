# Reconstructing original QueryStream as executable mathematics

**Status:** incremental research, **not** a complete computable #SAT algorithm.
**Source pin:** [openai/math `4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT).
**Acceptance environment:** Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
**New Lean:** [`QueryStreamConstructivePairs.lean`](../proofs/QueryStreamConstructivePairs.lean).

## What is the original program?

The authority is
[`SqrtLogSpace/QueryStreamProgram.lean`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamProgram.lean),
not any Rust program or a definition of #SAT obtained by enumerating assignments.
Its source structure is:

```text
QueryStreamProgram.program = StructuredCalls.compiled command 330 323
  command = HighQueryAdapter.prepareHigh;
            (QueryAssembler.Nodes.initializeNodes;
             QueryNodeFinish.guardCursor;
             while register 37:
               QueryAssembler.Nodes.beginNode;
               NativeLayoutLoad.command;
               SignatureHeadLoader.bootstrapProgram (lifted);
               PairNativeSetup.setupCaller;
               DifferencePairsProgram.command pairPorts pairCallback;
               QueryNodeFinish.command);
            QueryReconstruction.command

  pairCallback = QueryExecution.PairStart.command;
                 SignatureTupleComplete.command;
                 QueryAssembler.commitPair
```

This is a *fixed structured finite bit-program description*, not a
`CNF → Nat` definition. The source is declared inside a
`noncomputable section`. That syntax alone neither establishes a mathematical
impossibility nor makes all its components genuinely nonconstructive.
[`StructuredCalls.compiled`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/StructuredCalls.lean)
already constructs finite instruction tables from source syntax, and
`StructuredCalls.eval_trace` connects successful source evaluations to traces.
Neither theorem supplies a *total input-to-output evaluator* or a uniform
resource bound for all encoded CNFs.

## Immediate dependency and noncomputability audit

This table covers the *immediate mathematical reconstruction frontier*, not
a claim to have exhaustively inspected every imported declaration in the much
larger source closure.

| Original declaration and source | Mathematical role / types | Present constructivity status | Missing exact mathematical step |
| --- | --- | --- | --- |
| `QueryStreamProgram.command`, `program`, [QueryStreamProgram](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamProgram.lean) | Fixed `Cmd 40 896`; `BitProgram.Program` with input 330 and output 323 | Defined in a `noncomputable section`; finite syntax and source compilation are specified | Total terminating evaluator on precisely encoded CNFs; full numerical meaning of returned stack 323 |
| `HighQueryAdapter.prepareHigh`, same closure | Decode actual conditioned high-assignment counter | Finite command; original execution evidence conditional on a prepared input | Explicit computable mathematical input preparation and all-input decoding theorem |
| `QueryAssembler.Nodes.initializeNodes`, `QueryNodeFinish.guardCursor`, [QueryAssembler](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryAssembler.lean) and [QueryNodeFinish](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeFinish.lean) | Encoded list of interpolation nodes, loop guard and cursor | Finite commands; some noncomputable *semantic state witnesses* rely on classical/state-extension functions | Extract computable node representation, preserve ordering, prove cursor termination and body invariant |
| `SignatureHeadLoader.bootstrapProgram`, `PairNativeSetup.setupCaller` | Bootstrap signed coefficient/cache and pair controller | Source program syntax available; fully executable mathematical correspondence not reconstructed here | Constructive signed coefficient and source cache equivalence |
| `DifferencePairs.fold`, [DifferencePairs](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DifferencePairs.lean) | Recursive ordered fold `(List (Option Bool) → α → α) → Nat → Nat → List (Option Bool) → α → α` | **Already total and computable**, by structural recursion on the remaining coordinates; no noncomputable replacement needed | For whole QueryStream, instantiate visit with the *actual* pair callback meaning |
| `DifferencePairsProgram.command`, [DifferencePairsProgram](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DifferencePairsProgram.lean) | Physical source DFS with four protected controller stacks | Finite command; a relational source theorem is available under an explicit callback invariant | Prove its specific `pairCallback` implements the corresponding mathematical `visit` |
| `BooleanDifferences.pairFamily`, [BooleanDifferences](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/BooleanDifferences.lean) | Finite mathematical family `(E,U)`, `U ⊆ E`, `|E| < J` | Finite `Finset` specification; potentially materializes exponential family if used operationally | Use as *proof* denotation, not executable callback enumeration |
| `QueryExecution.PairStart.command`, `SignatureTupleComplete.command`, `QueryAssembler.commitPair` | Source pair callback, attained-signature visit and signed accumulation | Fixed source commands; `SignatureTupleComplete` is also written inside a `noncomputable section` | **Primary numerical frontier:** constructive decoded callback result; source program/semantic fold correspondence, including sign and ring precision |
| `QueryNodeFinish.command` and original moments readout | Emit ordered coefficient words and advance node cursor | Source readout shell and unary iteration cost already proved under explicit `Visits` premises | Prove actual numerical row, coefficient value, and stream bytes |
| `QueryCountReconstruction.jets_of_outputs`, [QueryCountReconstruction](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryCountReconstruction.lean) | Proof that emitted output bytes describe required `Q×J` Hermite jets | Proof uses `classical` and `choose` on per-node code existence; **not** a runtime choice in `QueryStreamProgram.command` | Implement a checked, finite coefficient-word parser and prove encode/decode correspondence with the *same emitted bytes* |
| `QueryReconstruction.command`, [QueryReconstruction](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryReconstruction.lean) | Node stream handoff, Hermite reconstruction, canonical count readback | Finite source command; conditional output correctness theorem already exists | Discharge `HasJets`, degree and modulus precision conditions from actual preceding computation |
| `QueryStreamCorrect.run`, [QueryStreamCorrect](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamCorrect.lean) | Conditional entire command evaluation and word output theorem | Existing theorem with substantial prepared-source/model/word-bound premises | Construct complete inputs, discharge assumptions, prove totality on arbitrary CNFs |
| `FiniteFallback.tableCount`, [FiniteFallback](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FiniteFallback.lean) | Finite lookup/count fallback | Explicit noncomputable finite tabulation | **Excluded** from reconstruction because replacing the core with count enumeration is not source faithful |

Two different issues remain distinct: (1) choice/noncomputability in
*proof-only state or witness constructions* and (2) the still-unverified
mathematical equivalence of a genuinely executable implementation of the
whole QueryStream. The audit does not assert that any listed numerical
operation is inherently noncomputable.

## Constructive result: original signed-pair order

The original source defines a ternary state for each coordinate:
`none` (outside support), `some false` (in `E \ U`), and
`some true` (in `U`), with `U ⊆ E` and `|E| < J`.
`DifferencePairs.fold` visits these pairs in source DFS order without
constructing the full `words` list.

The new `weightedSum` uses **exactly that original function** with the
callback `acc ↦ acc + weight(pair)`.
`weightedSum_eq_pairFamily` instantiates the source's already-proved
`DifferencePairs.fold_decode_sum` to establish

```text
weightedSum weight n J =
  ∑ (E,U) ∈ BooleanDifferences.pairFamily n J,
    weight (DifferencePairs.encodePair E U).
```

`signedSum` uses `(-1)^(number of some-false coordinates)`.
`differenceSign_encodePair` proves that the count of those coordinates
is exactly `E.card - U.card` for `U ⊆ E`; hence
`signedSum_eq_original_difference` identifies this executable sum
with the source's exact Boolean finite-difference sign, **not merely**
with a bit-encoded signed pair family.

**Scope:** this is not an algorithm for producing `weight` from
`QueryStreamProgram.pairCallback`. Correctness of the actual signed
coefficient callback is the first significant unresolved refinement.

## Exact visit complexity and explicit exponential regime

The unchanged source establishes the callback count recurrence

```text
P(n,0) = 0
P(0,J+1) = 1
P(n+1,J+1) = P(n,J+1) + 2 P(n,J).
```

and proves

```text
P(n,J) = ∑ (k < J) 2^k · C(n,k).
```

When `n < J`, the new induction yields `P(n,J) = 3^n`;
the original recursive call count satisfies `3^n ≤ calls(n,J)` in that
regime. This is an exact exponential *source-iterator* witness, not a
lower bound on every QueryStream instance: a valid algorithm may choose a
strictly smaller `J`, use additional cancellation, or summarize callbacks
without individually visiting them. Such a change would require a
separate algorithm and source-correspondence proof.

The upstream bound `calls(n,J) ≤ (3n+1)P(n,J)` for `J>0` counts
recursive nodes, **not bit operations**. Each prefix extension
`pre ++ [symbol]` costs at most `O(n)` list work; additions cost a
function of accumulated coefficient bitlength; each callback has its
own potentially expensive source algebra. A conditional upper estimate
for the new direct fold is therefore

`O(n · calls(n,J) + P(n,J) · (W + A))`,

where `W` bounds callback arithmetic work and `A` bounds accumulator
addition bit cost. This is a mathematical cost decomposition, *not yet
a kernel-checked total bit-complexity theorem*. The whole QueryStream's
precision, coefficient growth and peak live objects remain open.

## Reconstruction and precision prerequisites

The pinned [`QueryCountReconstruction.run_space_of_outputs`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryCountReconstruction.lean)
requires each of `Q` emitted nodes to supply exactly `J`
coefficient codes with bytewise identity to the emitted stream and the
required polynomial coefficient interpretation. For the recovery target,
its hypotheses include

```text
target.natDegree < Q * J
count ≤ multiplicity * 2^ambient
multiplicity * 2^ambient < 3^t
target.eval 0 = (count : extension-ring)
```

These are mathematical *preconditions*, not proofs that runtime chosen
parameters always satisfy them. Establish the executable coefficient
parser and the true `pairCallback` semantic specification before deriving
uniform truncation/reconstruction bounds from a guessed schedule.

## Checks, claims and remaining work

The Lean file includes finite `by decide` examples and `#eval` for
0, 5 and 27 callbacks and a nontrivial signed cancellation. An independent
enumeration of ternary *pair states* (not satisfying assignments) confirmed
these sample values, with the following expected rows:

| `n` | `J` | Pair callbacks | Signed unit-weight sum |
| ---: | ---: | ---: | ---: |
| 0 | 0 | 0 | 0 |
| 0 | 1 | 1 | 1 |
| 2 | 2 | 5 | 1 |
| 3 | 2 | 7 | 1 |
| 3 | 4 | 27 | 1 |

The isolated [CI run #45211897207](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/45211897207)
**passed** against the unchanged pinned source at commit `7ebdf6b`, including
all new theorems, executable examples and `#print axioms`. The reported
axioms were subsets of `propext`, `Classical.choice`, and `Quot.sound`;
**no `sorryAx`** appears. Choice is in proof-level finite-set lemmas;
the concrete `weightedSum` and `signedSum` operations are computable.
Existing upstream theorems are reused rather than silently reproved. No CNF-wide input evaluation, original
whole-program equality, numerical coefficient reconstruction, universal
termination or subexponential bit-cost theorem is established by this PR.

**Next precise proof:** Define the mathematical `visit` of the actual
`QueryStreamProgram.pairCallback`, then discharge the callback invariant in
[`DifferencePairsRelational.CallbackSpec`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DifferencePairsRelational.lean).
Only after that connection should the numerical callback replace the
parameterized `weight` in the computable contraction.
