# Pinned Lean capture and offline replay

The original `openai/math` Git submodule is **read-only**. These sidecar probes
import the original Lean definitions and execute the original `BitProgram.step`
(or `BitProgram.execInstr`, definitionally the same single-step transition).
The probes are **not** substitute implementations of the algorithms.

This branch contains five existing source-executed Rust-conformance trace
producers (copied from the Rust reference tree) and a deeper finite-machine
observer. Together they cover nine independently resumable capture stages.
They are not a complete trace of `Native.countingProgram` and make no assertion
about the ETH proof or TM2 microstep resource bounds.

## First capture

```bash
git checkout lean/upstream-reference
git submodule update --init upstream/openai-math
# First restore and verify the pinned Lean 4.34.1/Mathlib build cache.
python3 instrumentation/source_inventory.py   # static source index; no Lean needed
python3 instrumentation/capture.py plan
python3 instrumentation/capture.py capture
python3 instrumentation/capture.py verify
```

The source inventory records every source module, SHA-256, imported module,
and lexical declaration location under `SubexponentialSAT`. Its declaration
list is a navigation aid, not an elaborated symbol table.

The capture script uses `lake env lean --run` in the upstream `lean/` project;
compiled imports are reused when the pinned `.olean` cache is complete.
No `lake update` or `lake build OAI` is performed by the capture runner.
The upstream source commit, source-tree hash, toolchain pin, Lean version,
Lake manifest hash, each probe hash, invocation, result status, output hashes,
per-stage coverage, source instruction/opcode counts, visited labels, peak
Boolean stack storage, elapsed time and process RSS peak are recorded. Each
stage writes gzipped stdout, stderr, and a metadata JSON checkpoint atomically.
`index.json` is updated after each successful stage. The `lean-captures/`
output directory is ignored by Git and can be archived in immutable storage.

## Run only the portion you need

```bash
python3 instrumentation/capture.py capture --stage native-query-prefix
python3 instrumentation/capture.py capture --stage machine-branch
python3 instrumentation/capture.py verify --stage machine-branch
python3 instrumentation/inspect.py --stage machine-branch --case mixed --step 15
python3 instrumentation/inspect.py --stage machine-branch --case mixed --code
```

Completed stages are validated and skipped. A crash, missing case, exhausted
fuel, nonzero Lean exit, mismatched pin, changed probe, or corrupted output
never qualifies as a completed checkpoint. A changed fuel budget or probe
requires an intentional `--replace` for the selected stage. Errors are
preserved in `runs/<stage>.failed.{stdout,stderr}` without a success marker.
A stage can also be rerun directly, for example:

```bash
cd upstream/openai-math/lean
lake env lean --run ../../../instrumentation/probes/machine_dump.lean branch mixed 100000
```

The direct command emits only the selected machine/case. The orchestrated
capture records the full fixed case matrix, with exact case completeness
required. For a complete capture, preserve the entire `lean-captures/`
folder, not just the legacy final-state summaries.

## What the record includes

- The **complete finite instruction table** for each deeply observed program,
  including opcode, physical operands and continuation label.
- Initial machine state, every executed instruction and **complete physical
  register/stack state after each step**, terminal state and exact source
  instruction count. Empty stacks are implicit; stack words are written
  top-first in Lean `List Bool` order. This supports offline step selection and
  exact prefix comparison without executing Lean again.
- Final-state traces from the five existing conformance probes covering high
  initialization, tuple iteration, query-prefix preparation, node entry,
  native layout loading, and pair setup. Those probes preserve their existing
  case matrices and raw wire formats for Rust comparator compatibility.

Runtime provenance is **not** a formal proof that restored `.olean` files were
built from the pinned source: compiled-cache provenance must be established
separately. The Lean compiler is not available in the minimal agent VM, and the
pinned Mathlib cache has been incomplete, so the Lean probes themselves need
execution in the restored Lean environment before the capture can be accepted
as a genuine independent oracle. Python orchestration tests are runnable now:

```bash
python3 -m unittest discover -s instrumentation/tests -v
```
