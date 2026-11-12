# Original high-query → leaf → DFS → outer counting Rust entrypoint

This integration targets the **actual original Lean command**, not a host-side
#SAT oracle. Pinned source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`
with Lean 4.34.1 and the repository's pinned Mathlib version.

## Composition

The source-derived wrapper is definitionally the original counting program:

```lean
compiled
  (Native.entryCommand cutoff
    (Native.outerCommand k (NativeLeafProgram.command k)))
  ABI.countStack ABI.answerStack
```

The original dependencies are:

- `HighQueryProgram.marked k` and `HighQueryProgram.accepted k`:
  the fixed physical query stream, including high-assignment iteration.
- `NativeLeafProgram.command k`: native terminal classification and
  nonterminal high-query count, outputting the entire count on stack 263.
- `DFSCountProgram.command k leaf`: startup, DFS loop, leaf calls,
  count accumulation and full count-word export on stack 256.
- `Native.outerCommand k leaf`: canonical setup, counting DFS and
  source-defined positivity, with the Boolean on stack 1216.
- `Native.entryCommand cutoff`: canonical frontend and original finite
  cutoff dispatch.

Do not collapse any of these commands to a Boolean success flag. The
LSB-first count word and positivity bit are separate physical outputs.

## Build

Restore the pinned original source and compiled Lean environment first,
using the existing `original-source-graph.yml` source setup. Then:

```sh
python3 rust/lean_eth_reference/tools/compile_native_count.py \
  --upstream upstream/openai-math \
  --lake-root instrumentation/lean-env \
  --rust-crate rust/lean_eth_reference \
  --output-dir /tmp/eth-count-build \
  --width 3 --cutoff 20 --require-certificate

/tmp/eth-count-build/eth-count \
  --max-steps 100000000 --max-stack-bits 2000000 < example.cnf
```

The builder produces a single executable `eth-count`, the source graph,
generated Rust source and a source-bound build receipt **only after** a
successful `lake` export and offline Cargo build. The optional certificate
flag also requires Lean to check that every source instruction and physical
transition matches the imported original program. Without this flag the
receipt explicitly states that the compilation is uncertified.

The executable reads DIMACS CNF on standard input and rejects clauses wider
than the compiled parameter `k`. It reports the machine's resulting
physical count word as a decimal integer, the positivity bit, instructions
executed and peak live bit-stack cells. It refuses unrecognized source
instructions, invalid port maps, malformed graphs, unsupported source
structures and exceeded execution budgets instead of returning a fabricated
result. The output is not a TM2 primitive trace or worst-case bit bound.

## Acceptance, not just compilation

The lightweight TDD suite is:

```sh
python3 -m unittest discover \
  -s rust/lean_eth_reference/tools \
  -p test_compile_native_count.py -v
```

The chosen `--cutoff 20` is a compile parameter, **not** evidence that 20
is the particular existential cutoff constructed by `Final.lean`.
That correspondence remains a separate Lean proof obligation.

The success criteria for this integration are stronger than those tests:
1. The original full declaration must elaborate in Lean under pinned source,
   without a synthetic host counting implementation.
2. The exported graph must contain **all** query, leaf, DFS, and outer
   control sites, including lifted original finite tables.
3. The full Rust executable must build and actually halt on representative
   source-supported DIMACS inputs, with the full count and positivity.
4. Source-derived Lean correctness and differential evidence must support
   these executions. Rust's source-graph hash alone is not certification.

**Current status:** a source-derived compiler, single-binary generator and
offline contract tests are committed. A complete original Lean graph
export, the whole-program kernel certificate and end-to-end compiled
execution have **not yet been established**. The existing exporter limits
finite leaves to 4,096 labels, total source sites to 50,000 and graph
depth/nodes; a large source composition may explicitly refuse at those
limits. Raising limits without addressing on-demand source generators
does not constitute completion.

No nonexponential worst-case complexity or ETH conclusion follows from
a successfully compiled program.
