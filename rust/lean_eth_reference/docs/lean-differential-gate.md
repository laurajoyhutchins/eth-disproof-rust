# Exact-source Lean/Rust differential gate

The literal Rust port must not be certified solely by Rust-to-Rust tests, copied expected output, or matching counts on a semantic oracle. Its source of truth is the unchanged `openai/math` checkout at `4eaee87548250b2682affda7d05d947c05554bae`, compiled with Lean **4.34.1** and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Run one bounded machine, then the existing five suites

From `rust/lean_eth_reference`:

```sh
scripts/verify-lean-differential.sh --lean-repo /path/to/openai/math --suite full
scripts/verify-lean-differential.sh --lean-repo /path/to/openai/math --suite all
```

The default `full` suite runs the **original imported** `SqrtLog.HighIncidenceProgram.Branches.program` and records the program counter, **every** Boolean register, **both** complete bit stacks, and the step index after each `BitProgram.step` from initialization to halt. It enumerates all masks of width 0 through 4, each with clean and dirty initial register/output-stack configurations: **62 cases**. There is no callback, host-side answer substitution, or hard-coded Lean trace.

The remaining five suites independently exercise the existing source-importing Lean observers and Rust trace binaries (`high`, `tuple`, `layout`, `nodes`, `query`). Their observations are narrower than full-state equivalence; they are supplementary checks, not a substitute for the full-state gate. Each can be rerun alone using `--suite NAME`.

The script checks the exact OpenAI and Mathlib Git revisions, a clean tracked upstream source tree, the pinned Lean/Rust versions, a successful **actual `import Mathlib`**, and fresh source target builds. It then independently executes Lean and Rust, validates complete fixture coverage and step sequence, compares traces, and writes `target/lean-differential/receipt.json` only after **all selected suites pass**. The receipt records source identities, the Rust revision, tool versions, and SHA-256 hashes of observed streams. Failed runs remove stale receipts.

To test the comparator alone without Lean, run:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
```

**Acceptance status:** Not green until a real pinned `import Mathlib` and a fresh imported-source differential invocation complete. Restoring Lean 4.34.1 alone is not equivalent to restoring the 8,548 original Mathlib compiled modules. Missing original modules must cause a failure, not a synthesized Lean result. This gate tests finite source-machine execution, not the complete native ETH theorem, TM2 primitive refinement, or worst-case bit complexity.
