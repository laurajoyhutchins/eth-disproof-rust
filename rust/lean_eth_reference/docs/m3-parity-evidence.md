# M3: imported Lean/Rust finite trace gate

Tracking: [#101](https://github.com/laurajoyhutchins/nonexp-sudoku/issues/101), [#109](https://github.com/laurajoyhutchins/nonexp-sudoku/issues/109).
This is one **partial acceptance increment**, not milestone-three completion.

The five standalone comparators accept caller-supplied text. Equality of two
files cannot certify that one was emitted by the original Lean program. The
new runner instead launches imported-source Lean and the Rust port separately,
then invokes each existing strict comparator. It checks the exact
[OpenAI source commit](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae),
all declared original Lean Git blobs, the declared Lean 4.34.1 compiler,
the matching Mathlib Git checkout (d13f23b723b8a846827a245b89c10fc7d3f11612),
and clean tracked worktrees. A receipt records the actual two commands, Rust
commit, source blob list, wrapper/comparator digests and output digests. It is
only written **after** each selected suite passes. A stale prior receipt is
removed before every run. The gate accepts **no externally provided trace
files**, and does **not** fall back to Rust-generated Lean surrogates.

## Offline tests (do not require Lean)

From rust/lean_eth_reference:

    python3 -m unittest discover -s scripts/tests -v

These tests run in scripts/verify-local.sh before fmt, offline Cargo tests,
and strict Clippy. They cover correct and wrong source hashes, missing files,
incorrect source/toolchain pins, traversal/empty manifests, Mathlib lock mismatch, stage uniqueness, and same-path refusal in all five comparators.

## Real source-executed verification (blocked pending complete Mathlib restore)

Restore the **existing** pinned 4.34.1 compiler and fully matching Mathlib cache,
and check out original openai/math at the source commit above. Do not use the
Lean 4.35.0 kit for this command. Run from this crate's clean committed tree:

    python3 scripts/verify-imported-lean-parity.py --lean-repo /path/to/openai-math --stage all --receipt /tmp/lean-rust-parity.json

Use --stage high, tuple, query-prefix, nodes, or layout-pair to check
an independently completed source stage. Each invokes the existing imported
Lean reference entrypoint with lake env lean --run, and its corresponding
native Rust trace executable with offline Cargo. Both must succeed, then the
strict per-stage comparator must succeed. The runner uses explicit subprocess
timeouts and fails closed if binaries, Mathlib, a source blob, or any fixture
are missing, or if traces disagree.

**This gate has not been run against an executable original Lean checkout yet.**
It reports no Lean/Rust equivalence result until actual execution succeeds.

## Acceptance boundary

| Requirement | Current status |
|---|---|
| Rust finite stage executables | Present in PR #96; combined-branch runtime tests not re-run here |
| Evidence-gate source pin, provenance and refusal behavior | Implemented; eight offline Python unit tests exercised locally |
| Original imported Lean/Rust fixture snapshot parity | **Blocked** by incomplete Mathlib 4.34.1 restoration |
| Full instruction table, PC, register, stack, protected frame and halting refinement | **Not established** by fixture snapshots |
| Complete query, native counter, independent CNF counting | Requires M1/M2 #104/#107/#108 |
| TM2 primitive microsteps, tape visits, bit-work and physical resource costs | Unimplemented; #110 |
| Preconditions, including W >= 1 + 2*A*R | Must be checked for exact end-to-end inputs under #111 |
| Proof/complexity of SqrtLogSpace/Final.lean:exact_count_and_sat | **Not established**; no ETH disproof claim |

The runtime receipt is evidence of **finite fixture snapshot equality only**.
It is not a full bisimulation proof, a checked source-level compiler
correctness proof, or an asymptotic complexity argument. The final M3 audit
must keep those distinctions explicit.
