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

Two original affine-factor families:

1. **Chain equality:** N equality edges connecting N+1 Boolean variables.
   The exact closed count is 2. Sequential and reverse folds have small
   intermediates; even-first activates multiple disconnected components and
   can require substantially larger interfaces before the gaps close.
2. **Circulant XOR3:** N three-variable parity factors on N cyclic variables;
   each factor uses \(x_i,x_{i+1},x_{i+\lfloor N/2\rfloor}\) modulo N
   (with stride at least 2). RHS bits are generated from an explicit witness,
   ensuring consistency. This is a **bounded-degree cyclic family**, not a
   proved expander. Counts and intermediate sizes are measured, not presumed.

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

The `peak_d` and `sum_d` fields separate maximum intermediate
representation size from aggregate stored representation sizes. The cumulative
cell count is a proxy, not a verified runtime complexity theorem. The
`elapsed_ns` observations are not deterministic across machines.

**Independent correctness evidence:** for small networks (chain <=9 edges,
circulant <=10 vertices) the CLI enumerates all original assignments and
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
