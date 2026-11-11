# Optimization annotation 001: defer power-word materialization

**Status:** proposed transformation, not implemented or benchmarked.

**Lean source:** [`LayoutProgram.powerCommand`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramPower.lean), pinned at `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

**Literal Rust anchor:** [`native_integer_cache.rs::power_command`](../src/native_integer_cache.rs), and its use through `make_power_command`. The reference implementation is **not** changed by this annotation. Branch baseline: `main@1c008a281773dfa979b8bc3c2eba7facb991af71`.

## Observation

The literal 2-register/2-stack program consumes a unary exponent `q` and produces the little-endian bit representation of `2^q` by pushing one true bit and then `q` zero bits. The materialized output has `q + 1` bits. This is a representation cost, not an observation about the complete ETH algorithm's complexity.

## Hypothesis

For consumers that operate algebraically on this power rather than inspecting every bit, keep a tagged value `Pow2(q)` and materialize the little-endian word only at a boundary that actually requires it. With a binary-encoded exponent, the tagged value occupies `O(log(q+1))` bits instead of `Theta(q)` bits. **This does not save the `Theta(q)` work of consuming the current unary input**, nor does it help if a downstream consumer necessarily reads or writes all `q + 1` bits.

The place to investigate first is `make_power_command` and its immediate downstream consumers, not an ungrounded replacement of the full native leaf.

## Acceptance criteria

1. Preserve the source-faithful interpreter and its Lean correspondence unchanged. Put candidate native/symbolic code behind a separate testable entry point.
2. For small `q` including 0 and edge cases, compare candidate materialization with the literal program's **entire final machine state** (output bit order, input consumption, registers, scratch, halt), not merely its numeric value. A representation-changing path may use a separate refinement relation, but must specify it explicitly.
3. Demonstrate that every optimized downstream consumer preserves exact observable output and refusal behavior; otherwise the optimization is local only.
4. Measure source steps, native cycles, peak allocated bytes, materialized bit count, and bit lengths separately. Compare with identical input and output obligations. Do not infer worst-case bounds from timings.
5. If the symbolic representation is claimed to improve asymptotic complexity, prove bounds for *all* transitions and conversions, including any forced expansion. Reject the claim if any required consumer invalidates those bounds.

## Evidence ledger

- Source/port correspondence: inspected in the pinned Rust file and source-linked program construction.
- Direct LLVM specialization: **not measured**.
- Native candidate: **not implemented**.
- Lean/Rust differential execution: **not established**.
- Complexity improvement: **not established**.

## Branch rule

This branch is a **source-linked optimization notebook expressed as Git history**. Each subsequent commit should isolate one specific annotated transformation, identify its exact Lean symbol and literal Rust anchor, distinguish a hypothesis from tested results, and include the smallest code/test/evidence change needed to evaluate it. Keep the literal port on `main` authoritative; do not silently rewrite the reference implementation or squash unrelated experiments into one commit. A passing compiler or faster benchmark alone is not a mathematical complexity result.
