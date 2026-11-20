# Signed quadratic projection over an affine receipt

This experiment extends the existing packed GF(2) affine eliminator and its independently replayed dense Boolean certificate. **There is no second row-reduction engine in this module.**

## Contract and supported scope

A single signed elimination step has **exactly one internal Boolean variable**. The new chain interface supports *several* ordered internal variables by running that step repeatedly, carrying the certified output boundary into the next stage. The shared assumptions remain affine equations, a quadratic Boolean ANF phase Q, and a nonnegative integer exponent k. It denotes the **integer** function

\[
M(b)=\sum_{x\in\{0,1\}}2^k(-1)^{Q(x,b)}[A(x,b)=c].
\]

The public method SignedOneBitRegion.eliminate() returns a boundary interface only after both layers pass verification:

1. The existing AffineRegion.eliminate_with_certificate produces a packed row-operation transcript and residual interface. Its existing EliminationCertificate.verify reconstructs and replays source equations in a separate dense Boolean matrix, checks pivot columns, and rejects tampering.
2. The signed extension adds a local phase rule, either FixedBySourceRow(i) with a selected source row solving x=ell(b), or Free when the internal column has no pivot. The checker does not use the producer's ANF substitution implementation.

The exact rules are:

- **Forced:** substitute x=ell(b) into the quadratic phase. There is one internal extension on each feasible boundary and the exponent remains k.
- **Free:** write Q(x,b)=Q(0,b) XOR xL(b), with affine L. The signed fiber sum is 2^(k+1)*(-1)^Q(0,b)*[L(b)=0]. The checker requires this additional affine boundary constraint and increments the exponent once.

Output includes independently replayed affine residual constraints, the signed-phase polynomial, an optional cancellation constraint, and a symbolic signed power-of-two value. Materialization to BigInt is explicit.

**Unsupported:** multiple internal variables inside a *single* certified step (the chain instead verifies them sequentially), input phases of degree above two, nonlinear equations, general sums of modes, and source-specific OpenAI/Anthropic adapters. Inputs outside scope refuse.

## Independent polynomial-time phase checker

The producer manipulates squarefree ANF monomials algebraically. The checker instead reconstructs the output phase from evaluations at **boundary Hamming weights zero, one, and two**:

\[
c=f(0),\quad \ell_i=f(e_i)\oplus c,\quad
q_{ij}=f(e_i\oplus e_j)\oplus f(e_i)\oplus f(e_j)\oplus c.
\]

Any squarefree degree-two Boolean polynomial is uniquely determined by these coefficients. Since substituting an affine function into a quadratic phase remains quadratic, matching these recovered coefficients to the claimed ANF certifies equality at **every** exterior assignment without enumerating 2^n boundary configurations. There are exactly 1+n(n+1)/2 evaluations for n boundary bits. The free-variable coefficient is independently reconstructed from its zero- and one-bit samples and checked against the claimed extra constraint.

A caller-configurable interpolation-sample budget enforces an **explicit refusal** rather than declaring an unverified output complete. For chained elimination it is checked against the **sum of all stage sample counts**, not merely each stage separately. A dedicated test rejects a two-stage chain that individually fits but cumulatively exceeds its budget. The shared affine producer/checker maintain their own existing resource checks.

This is a Rust implementation of a standard quadratic interpolation argument, backed by independent tests. The existing pinned Lean [quadratic-interface proofs](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/364) kernel-check the local free/forced projection algebra. **The interpolation uniqueness theorem is now kernel-checked** in pinned Lean 4.34.1: [IndependentQuadraticLowWeight.lean](../../eth/proofs/IndependentQuadraticLowWeight.lean) proves the zero/singleton/doubleton coefficient recovery and all-boundary equality. [Exact-head workflow #44431012618](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44431012618) passed without `sorryAx`; the corresponding [root Rust workflow #44431012599](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44431012599) passed. **Native Rust-to-Lean implementation correspondence remains open.** Rust testing alone does not establish them.

## Run

From the repository root:

    cargo test --manifest-path experiments/egg-contraction-optimizer/Cargo.toml signed_affine

The standalone CI runs the full crate test suite. Tests independently enumerate both internal assignments at every external setting on random small systems; check forced and free projections; detect tampered affine receipts, phases, constraints and exponents; exercise a 130-bit exterior boundary; and confirm that too-small verification budgets refuse.

## Connections and next step

- [Affine transcript and packed-row Lean proofs](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/affine-elimination-certificates.md)
- [Quadratic signed-phase Lean foundation](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/quadratic-sign-boundary-interfaces.md)

## Lean executable local witness and Rust coefficient records

In [IndependentQuadraticLowWeight.lean](../../eth/proofs/IndependentQuadraticLowWeight.lean), the executable \`checkSamples\` compares two typed quadratic coefficient structures at the zero, singleton and doubleton supports. \`checkSamples_sound\` proves that acceptance implies phase equality at **all** boundary assignments, and \`checkSamples_sign_sound\` lifts it to the exact integer sign. The theorems \`checkedFreeLocalExact\` and \`checkedForcedLocalExact\` combine this check with the exact one-bit signed-fiber identities. They are **conditional on explicit source semantics**: the source must truly split into the supplied quadratic base plus the internal mixed coefficient, or agree with the supplied expected phase after a forced affine substitution. The checker cannot establish that premise merely by believing a witness from Rust.

The [pinned acceptance workflow #44639967898](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44639967898) successfully kernel-checked those theorems on a fixed green affine base, with only standard Lean axioms and no \`sorryAx\`. [Root Rust workflow #44639967947](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44639967947) passed at the same source head.

In native Rust, the independent verifier now returns a \`QuadraticCoefficientWitness\` containing a constant, one Boolean coefficient per boundary coordinate, and strictly sorted, distinct quadratic index pairs. Its evaluator rejects malformed or out-of-bound pairs rather than trusting an arbitrary external object. \`SignedVerificationReceipt.phase_coefficients\` carries that concrete coefficient record. \`SignedChainReceipt.checked_steps\` carries the per-step checked records in elimination order, alongside aggregate sample and row-operation counts. Test oracles compare every intermediate record's sign phase against the output ANF on small assignments.

These are concrete data for a future **Lean-to-Rust representation refinement**. No theorem yet proves that native \`BTreeSet<Vec<usize>>\` parsing, integer/index arithmetic, interpolation loops, affine-row transcript replay, or compiled Rust evaluation exactly implements the Lean specification. The acceptance theorem is a typed mathematical implication, not a proof of all machine code.

## Repeated, replay-checked signed elimination

The Rust `SignedMultiRegion` represents an ordered set of internal variables and a single quadratic phase over those variables and the external boundary. `eliminate_with_certificate` first views all but the first internal variable as temporary boundary ports. It repeatedly:

1. Invokes the **same** one-bit affine packed eliminator and independently checks its row-operation receipt and quadratic phase;
2. Converts the verified affine residual equations and any newly introduced signed-cancellation equation into source rows for the next internal bit, preserving phase and multiplicity;
3. Stores the verified output, its signed receipt and ordered port set as one chain step.

`SignedChain.verify` independently starts at the original source and replays **every** step, reconstructing each successor's inputs from its predecessor's certified output. It refuses missing, reordered or tampered stages and can enforce an explicit phase-sample budget. The returned final interface has exactly the original external boundary ordering.

The pinned Lean [`IndependentSignedComposition.lean`](../../eth/proofs/IndependentSignedComposition.lean) now **kernel-checks exact all-context composition for an arbitrary finite sequence of locally exact integer-valued Boolean-fiber eliminations**. [Exact-head Lean workflow #44615362237](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44615362237) passed at [commit dc6d728](https://github.com/laurajoyhutchins/eth-disproof-rust/commit/dc6d728181dd4d67fe4f7d26a002cddd386a6d8c); all printed axioms are standard Lean axioms with **no sorryAx**. The theorem remains **conditional on local correctness witnesses** and does not formally certify that the native Rust receipts instantiate those premises. The [root Rust run #44615362202](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44615362202) also passed at that head.

The new Rust tests independently enumerate up to five internal bits for small regions, check all external assignments, verify that a cancellation constraint generated in one step becomes the *next* step's forced affine pivot, and reject altered intermediate phases, missing stages, changed exponents and too-small budgets.

**Still open:** a formal Lean-to-Rust receipt refinement, a whole-machine correctness proof, total bit-operation and peak-memory bounds, general sums of modes, source-specific OAI/Anthropic adapters, and worst-case mode-growth results. Exact local and compositional semantics alone do not imply subexponential general #SAT.

## Connections and next step

- [Affine transcript and packed-row Lean proofs](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/affine-elimination-certificates.md)
- [Quadratic signed-phase Lean foundation](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/quadratic-sign-boundary-interfaces.md)

The next mathematical milestone is a **representation-refinement theorem** that connects the Rust phase, row and chain receipts to Lean's verified local exactness premises. Count checker work, coefficient bits and peak memory before drawing efficiency conclusions. No general subexponential #SAT claim follows.

## Independent native-to-Lean semantic oracle (November 20)

The draft now includes `checkNativeInstance` in
[`IndependentQuadraticLowWeight.lean`](../../eth/proofs/IndependentQuadraticLowWeight.lean).
It takes **explicit** source quadratic monomial indices, original affine equation
occurrences, an output phase and residual/cancellation rows, exponent, and the
checked sparse coefficient witness. It evaluates the *integer-valued* signed sum
over the one internal bit and compares it with the proposed output **at every
boundary assignment**. `checkNativeInstance_sound` states that an accepted
instance has that exact equality at every assignment. `checkNativeInstance_receipt_sound`
also states the output's raw monomial evaluator agrees with its decoded
coefficient record. These are independently specified Lean semantics, not
premises copied from the native verifier.

The Rust `SignedOneBitRegion::lean_oracle_example` emits only numeric
coordinate indices and Boolean literals from a verified native source/output,
never untrusted variable names as Lean syntax. The
`emit_signed_native_oracles` binary generates free-cancellation and forced
pivot cases. Pinned CI concatenates those generated data propositions with the
reference Lean source and checks them using `by decide`. A native positive
receipt cannot make a false Lean arithmetic equality true. The job retains
the earlier independent **affine** native-audit gate on the parent branch.

**Scope limitation:** This is an *independent, exhaustive cross-language
instance check*. It is intentionally exponential in the number of boundary
ports, and the generator has an explicit caller-supplied port budget. It
does **not** prove that the Rust serialization faithfully reflects a separate
authoritative input, that every native accepted result passes this Lean check,
or that the compiled Rust program refines the Lean polynomial-time checker.
A scalable universal native refinement, global bit cost, peak memory and any
ETH consequence remain open. Until its exact-head workflow passes, the newly
added Lean declarations and Rust-to-Lean integration are unverified source.

The source branch is restacked on the current affine-audit parent, without
dropping either independent proof gate.
