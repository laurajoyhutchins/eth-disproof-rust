# Optimization experiment 002: power words as exponents

**Status:** locally tested *isolated* representation change, not an end-to-end
algorithmic speedup.

**Pinned source:** [`LayoutProgram.powerCommand`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramPower.lean).

**Literal Rust oracle:** `src/native_integer_cache.rs::power_program` and
`make_power_program`. Neither was changed.

## Why this experiment exists

The source constructs little-endian `2^q` by physically writing a `true`
bit and then prepending `q` zeros. It produces a `q+1`-bit word even when
the next operation only needs the exponent, selected bits, or multiplication
by another power of two.

For consumers using only these observations, keep `Pow2(q)`. The identity

```text
2^a * 2^b = 2^(a+b)
bit_i(2^a) = (i == a)              [little-endian]
word_len(2^a) = a + 1
```

justifies exponent addition, random bit reads and length queries without
constructing any zero-filled intermediate word. This requires no claim
about source instruction equivalence during the deferred interval.

## Exact boundary and counterexamples

- The independent candidate lives in `src/deferred_power.rs`, never in
  the literal BitProgram compiler.
- For a **standalone** power machine, final materialization preserves the
  entire final machine configuration: the input stack is consumed; the
  original destination suffix is retained; the result is prepended in
  source order; both registers are false; the machine has halted.
- The physical `IntegerCache.makePower` first removes one unary element.
  Its clean-scratch output is `Pow2(max(q-1,0))`, not `Pow2(q)`.
- If the next consumer needs the complete word, at least `q+1` output
  bits must still be written. A unary input also costs `Omega(q)` to
  traverse or dispose of. This experiment **does not** remove either cost.
- Different intermediate machine states, source instruction counts, and
  source-level resource refusal are intentionally *not* claimed equivalent.
  The optimized path has a separate representation/refinement relation.
- Checked exponent overflow and output capacity refusals are explicit;
  refusal must not partially alter the output.

## Evidence (bounded and reproducible)

`tests/deferred_power.rs` compares all final machine fields against the
literal interpreter for `q=0..96`, both input bit values, three preexisting
output suffixes, and dirty initial registers. It checks clean-scratch
`makePower` outputs for `q=0..64`, representation composition at 900,000
bits, overflow, and nonmutating capacity refusal.

Offline Rust 1.99.1 verified formatting, the four new differential tests,
and strict Clippy against the user's independently restored v0.19.0 Rust
snapshot. That is **not** an exact checkout of this branch; full combined
branch CI and a genuine Lean execution comparison remain outstanding.
There is no measured end-to-end speedup.

## Next falsifiable question

Trace the *first production consumer* of stack 2 in
`LayoutProgram.IntegerCache.program`. If it reads every output bit, the
deferred representation is merely an API change. If a consumer composes
powers or uses only a sparse set of bits, implement that consumer as a
separate experimental command and compare its complete externally
observable outputs and resource costs to the original.
