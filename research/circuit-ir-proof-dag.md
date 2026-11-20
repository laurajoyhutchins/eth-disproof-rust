# Adaptive Certified Contraction: typed arithmetic circuit proof DAG

**Status:** semantic foundation under development. No fast #SAT algorithm or
OpenAI packet-algorithm lowering is established by this module.

## Mathematical object

The circuit IR at
[`instrumentation/lean-env/ACC/Circuit.lean`](../instrumentation/lean-env/ACC/Circuit.lean)
has **explicit** integer scalar, source factor, addition and multiplication
gates. `sumList`, `prodList`, `sumFinset` and `prodFinset` lower finite
algebraic combinations into that syntax. An atom valuation supplies only one
source factor, never the whole count or network contraction.

The source adapters at
[`eth/proofs/IndependentCircuitSource.lean`](../eth/proofs/IndependentCircuitSource.lean)
build these circuits from pinned definitions:

- **Anthropic:** the actual `Groundwork.Network` node states, node weights,
  allowed edge labels, and two endpoint factors. The evaluation theorem
  identifies this circuit with the original `N.value`. By applying the
  original pinned `Groundwork.Network.value_merge`, a separate theorem proves
  that compiling a merged network preserves the circuit evaluation.
- **OpenAI:** the actual pinned `SAT.CNF` semantics, with one atom per
  clause and full Boolean assignment, and explicit arithmetic products over
  clauses and sums over assignments. The evaluation theorem identifies this
  exhaustive circuit with `SAT.count`. This is a semantic starting point,
  **not** a compilation of the OpenAI packet program.

The core IR is a **tree**. It can be exponentially large and does not yet
represent shared nodes. A DAG backend, structural hash-consing, circuit
extraction, and cost-verified optimizers are further work. No `#SAT` oracle
is hidden in a gate.

## Dependency DAG

```mermaid
flowchart TD
  N["Pinned Anthropic Network.value"] --> NF["Source factor lowering"]
  S["Pinned OpenAI SAT.count"] --> SF["Clause factor lowering"]
  IR["Typed scalar/atom/add/mul circuit"] --> NF
  IR --> SF
  NF --> NV["Circuit evaluates to Network.value"]
  SF --> SV["Circuit evaluates to SAT.count"]
  VM["Pinned Anthropic value_merge"] --> NM["Circuit preserves merged-network value"]
  NV --> NM
  L["Boundary encode/decode retraction"] --> LC["lower_sound"]
  CL["Representable intermediate closure"] --> CMP["lower_comp"]
  L --> CMP
  NM --> Q["Native quotient network Q(N)"]
  Q --> QS["Allowed state images + fiberwise weights"]
  VM --> QS
  QS --> SQ["Full observational merge/quotient square"]
  SQ --> R["Network rewrite interface"]
  CMP --> R
  R --> D["Certified shared-DAG execution"]
  D --> CT["Exact #SAT theorem"]
  SV --> CT
  CT --> COST["Constructive total bit-cost theorem"]
```

### What each edge proves

1. **Source-factor lowering:** exposes every original factor as a circuit atom.
   It does *not* assert compression or runtime efficiency.
2. **Semantic evaluation:** multiplication and finite summation match the
   source's integer contraction.
3. **Anthropic merge:** the original source theorem ensures value preservation
   despite different node and atom types after grouping. This is equality
   under the *designated* source valuations, not a polymorphic rewrite valid
   under arbitrary valuations.
4. **Boundary composition:** `lower_comp` holds only when the intermediate
   state is representable. A two-coordinate counterexample demonstrates why
   the closure hypothesis cannot be omitted.
5. **DAG simulation:** still missing. Requires typed node identity, sharing,
   an acyclic evaluation order, and a per-node proof-carrying rewrite relation.
6. **Subexponential cost:** still missing. Requires constructive compression,
   resource-accounted planning, coefficient bit bounds, and a complete
   recurrence. Semantic equivalence is insufficient.

## Context-uniform quotient through Anthropic merge

[Boundary quotient source proof](../eth/proofs/IndependentBoundaryQuotient.lean)
defines an explicit state map \(q : \sigma\to K\) and a representative
\(r : K\to\sigma\). Its source-side hypothesis is

\[
\forall a,b,s,t,\quad f_{ab}(s,t)=f_{ab}(r(q(s)),t).
\]

For an Anthropic node \(a\), the ACTUAL `Network.toInst` table entry is

\[
T_a(\theta)=
 \sum_{s\in S_a} W_a(s)\prod_{b\ne a}
 [\theta_b\in D_{ab}]\, f_{ab}(s,\mathrm{dec}_{ab}(\theta_b)).
\]

The quotient weights aggregate **all** original states with the same
label, rather than replacing their weights with a representative:

\[
\bar W_a(k)=\sum_{s\in S_a:q(s)=k}W_a(s).
\]

The local exact identity, for **every** outside assignment \(\theta\), is

\[
\boxed{
T_a(\theta)=
\sum_{k\in q(S_a)}\bar W_a(k)
\prod_{b\ne a}
 [\theta_b\in D_{ab}]\,
 f_{ab}(r(k),\mathrm{dec}_{ab}(\theta_b)).
}
\]

This is a true non-injective quotient: different states may share one
boundary class, while their weights are added. It is not merely equality
of the completed network's scalar contraction.

### Full quotient/merge commuting square (verified)

The **native** `quotientNetwork N q r` uses state sets \(q(S_a)\),
fiber-summed weights \(\bar W_a\), original labels and capacities, and
the outgoing factor \(f_{ab}(r(k),t)\). The source-facing theorem
`quotientNetwork_toInst` proves equality of every outgoing
`Network.toInst` table entry between \(N\) and its quotient.

Anthropic's original `Network.merge color defaultState defaultLabel`
builds merged states as function-valued tuples. The lifted quotient is

\[
q^G(z)(a)=q(z(a)),\qquad r^G(k)(a)=r(k(a)).
\]

**The full observed network square is now proved** under factor invariance:

\[
\boxed{
\operatorname{toInst}\bigl(\operatorname{merge}(Q(N))\bigr)
=
\operatorname{toInst}\bigl(Q(\operatorname{merge}(N))\bigr).
}
\]

This equality is uniform over all external instance label sets and
decoders. The proof goes beyond the earlier scalar equality:

1. `quotient_merge_states_commute`: the *admissible* merged state
   sets are equal; this is an exact image-of-tuples theorem.
2. `tuple_fiber_product`: a weighted sum over the fiber of a
   merged state is the product of the individual state-fiber sums.
3. `quotient_pair_interaction`: the actual source `Network.Ψ`
   is invariant under representative replacement at both ends.
4. `quotient_merge_weight_on_states`: merged node weights agree
   on **admissible** states, using the previous two lemmas.
5. Factors, `Θ` labels and capacities agree componentwise,
   giving `quotient_merge_network_agreement`.
6. `NetworkAgreement.toInst` derives the final context-uniform
   `quotient_merge_toInst_commutes` for the actual pinned source.

It would be incorrect to require the arbitrary `W` functions to be
identical on states forbidden by `S`; those entries are not read
during contraction. The proved equivalence is exact observational
network equivalence, not literal structure equality at invalid inputs.

**Evidence:** [pinned Lean 4.34.1 run #44109954836](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44109954836)
on commit `d9304a4fd760b1709b41f868a4adb8ca24892a49`.
All three workflows passed. The new `#print axioms` declarations show
only `propext`, `Classical.choice` and `Quot.sound`, no `sorryAx`.

### An obstruction at OpenAI's zero deformation

The October 25 appendix specifies a Cauchy packet deformation satisfying
\(W(0)=I\). The induced binary port glue at \(T=0\) is the exact identity
kernel \(K(Y,X)=\mathbf1[Y=X]\).

The generic Lean theorem `identity_kernel_forces_injective_labels`
proves that any **state-identification** quotient whose representative
preserves every identity-kernel entry has injective labels. Therefore
there is no nontrivial state merging of that full identity interface.

This does **not** rule out correlated linear operators, spectral modes,
symbolic circuits, or exploiting restricted/weighted contexts. It
does prevent automatically transferring our Anthropic factor-class
compression to the OpenAI packet glue.

### Constructive/computational limitations

The proof uses finite images and fiber sums. It establishes no bound
on the time to discover \(q\), the class count \(|q(S_a)|\), the work
to enumerate the fibers, the size of a merged state, or the final circuit.
The best-case strict compression (two distinct Boolean states to one class)
is elementary; it does not imply a uniform reduction on arbitrary SAT
networks. The OpenAI packet/mode transform is not an instance of this
proof until its corresponding factor invariance is independently shown.

## Specific next proofs

| Milestone | Lean-level requirement | Acceptance condition |
| --- | --- | --- |
| C1 | Arithmetic tree evaluator and finite-fold lemmas | Lean kernel check, no admissions |
| C2 | Pinned Anthropic `Network.value` and `value_merge` adapter | Kernel check, exact original import |
| C3 | Pinned OpenAI `SAT.count` adapter | Kernel check, unused variables included |
| C4 | Typed shared DAG | Exact evaluation, acyclicity, sharing without recomputation |
| C5a | Anthropic factor-invariant quotient after merge | Verified in pinned Lean | 
| C5b | Native quotient/merge observational network square | Verified in pinned Lean for all admissible states and external toInst tables |
| C6 | OpenAI source-defined packet transform | Original packet constructor, factor/port identities, precision and routing |
| C7 | Combined recursion, complexity | Full constructive bit and peak-space recurrence |

`C1-C3` and `C5a-C5b` are verified under their exposed assumptions.
Neither a shared executable DAG, a source-derived OpenAI packet adapter,
nor a new bit-complexity bound follows from these semantic theorems.

## Toolchain and verification

The existing `lean-independent-formulations.yml` workflow pins Lean 4.34.1
and Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`, fetches the
unaltered OpenAI and Anthropic source snapshots, and checks the new modules.
The workflow rejects `sorry`/`admit` in the new source adapter and core IR.

Keep the distinctions between source identity, mathematical equivalence,
proof of executable correspondence, and total complexity explicit.
