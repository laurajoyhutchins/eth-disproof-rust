# Contraction order study (affine networks)

Run from the repository root:

```sh
cargo test --manifest-path experiments/egg-contraction-optimizer/Cargo.toml
cargo run --quiet --manifest-path experiments/egg-contraction-optimizer/Cargo.toml \
  --bin affine-order-study -- --sizes 8,16,32
cargo run --quiet --manifest-path experiments/egg-contraction-optimizer/Cargo.toml \
  --bin affine-order-study -- --sizes 8,16,32,64 --summaries-only
```

The program prints machine-readable JSON Lines. It runs **three deterministic
left-fold schedules on exactly the same factors**: sequential, reverse, and
even-indexed factors first. It explicitly maintains the set of ports referenced
by unprocessed factors or preserved as outputs. Only ports not in that live set
are summed out. All merges use the existing independently replay-checked
affine solver. An unsupported count or resource limit causes explicit refusal.

Three original affine-factor families:

1. **Chain equality:** N equality edges connecting N+1 Boolean variables.
   The exact closed count is 2. Sequential and reverse folds have small
   intermediates; even-first activates multiple disconnected components and
   can require substantially larger interfaces before the gaps close.
2. **Circulant XOR3:** N three-variable parity factors on N cyclic variables;
   each factor uses \(x_i,x_{i+1},x_{i+\lfloor N/2\rfloor}\) modulo N
   (with stride at least 2). RHS bits are generated from an explicit witness,
   ensuring consistency. This is a **bounded-degree cyclic family**, not a
   proved expander. Counts and intermediate sizes are measured, not presumed.
3. **Free amplifiers:** each of N disconnected factors has one unconstrained
   hidden bit u_i and one unconstrained exposed port x_i. Closing all
   variables produces exactly 2^(2N) assignments. This deliberately stresses
   coefficient/count bit length B without increasing the retained interface D.
   The closed count is huge as an integer, but its exact binary representation
   takes only O(N) bits.

The study records a stage for every consumed factor and a final summary for
each schedule:

- \(D_k\): ports + residual parity rows + incidences. This counts the
  **actual explicit interface maintained by this code**, including redundant
  rows when present, not the shortest possible encoding.
- \(B_k=f_k+1\): a **conservative** upper bound on the bit length of nonzero
  fiber multiplicities, which can overstate inconsistent interfaces.
- \(C_k\): logical matrix cells supplied to a merge, rows × (ports + 1).
  This measures source matrix shape, not CPU bit-operations or peak live RSS.
- Incremental and cumulative XOR operations and independent replay steps,
  plus observed elapsed time over each whole fold (including leaf construction).

The `peak_d` and `sum_d` fields describe the maximum and summed sizes
of the **active left-fold accumulator only**. They exclude simultaneously
stored unmerged leaves, certificate memory, and temporary solver workspace. The cumulative
cell count is a proxy, not a verified runtime complexity theorem. Because
GF(2) coefficients are just bits, this suite does **not** exercise coefficient
height explosion in general integer or symbolic interfaces. The new free
amplifiers exercise exact **multiplicity bit-length growth** without pretending
that a 2^(2N) integer requires exponential storage. The
`elapsed_ns` observations are not deterministic across machines.

**Independent correctness evidence:** for small networks (chain <=9 edges,
circulant <=10 vertices, free amplifiers <=6 factors) the CLI enumerates all original assignments and
compares the exact count. The unit tests also check all external assignments
on a two-port boundary, at many small sizes. Large runs compare three plans
but do not have a genuinely independent large-instance oracle.

**Research question:** Does representation closure imply efficient contraction?
For this affine-only representation, exact elimination has polynomial matrix
cost and the size is polynomial in its explicit row/port dimensions.
Nevertheless poor elimination order can cause unnecessary intermediate growth.
No conclusion follows about general CNF, nonlinear eight-square identities,
truncated symbolic moments, or an ETH counterexample.

Resource options are `--max-merge-cells` and
`--max-total-merge-cells`. Existing independently guarded affine
producer/checker budgets also apply. No exponential fallback is invoked.

Related: [COMPOSITION.md](COMPOSITION.md), [COUNTING.md](COUNTING.md).

## Live-port invariants and Rust witness (November 19)

The standalone Lean module `eth/proofs/IndependentLivePortFold.lean`
distinguishes the **set-theoretic liveness calculation** from the
**numerical meaning** of a boundary interface.

For already processed variable support `S`, next factor port support `T`,
future support `U`, and required external output `O`:

```text
live(S, T ∪ U, O) = S ∩ (T ∪ U ∪ O)
kept = (current_ports ∪ T) ∩ (U ∪ O)
```

If `current_ports = live(S, T ∪ U, O)`, Lean proves
`kept = live(S ∪ T, U, O)`. The proof is Boolean set algebra,
not a GF(2) assumption. A Lean induction applies this update across
an **arbitrary list of factor port sets**.

There is a deliberate startup exception: the Rust fold starts with the
first factor's entire declared port set, not a normalized live set.
Consequently the live-set equality need not hold at `step = 0`.
The first merge removes stale ports, after which the invariant holds.
The Lean theorem `runPorts_from_raw_first` handles this exact
initialization.

The Rust test `rust_kept_ports_refine_live_set_update_at_every_merge`
recomputes the union of all processed factor port sets independently,
intersects it with future/output support, and compares that expected
set against the **actual retained names in each recorded stage**.
The test exercises all three schedules, all three factor families,
sizes 3..10, and both closed and two-port-output contexts. This is
finite differential evidence that the Rust set implementation follows
the Lean definition, not a proof of the Rust implementation.

Separately, `independent_private_fold_correct` proves by induction
that the nested direct sum of any finite sequence of independently
quantified private factor blocks equals their product of exact local
fibers at a fixed shared boundary assignment, over an arbitrary
commutative semiring. This does **not** establish full variable-sharing
semantics for general cyclic graphs: it must still be composed with an
exact theorem for elimination over overlapping scopes and with the
Rust GF(2) certificate/refinement boundary. The existing small-instance
CNF and affine oracles remain independent implementation evidence.
