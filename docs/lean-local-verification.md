# Local pinned Lean primitive verification

The source is pinned to `openai/math` commit
`4eaee87548250b2682affda7d05d947c05554bae`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and **Lean 4.34.1**.

The available offline Lean **4.35.0** toolchain is NOT interchangeable with
this pinned build. First restore or bootstrap a Lean 4.34.1 toolchain and the
matching upstream Git checkout and Mathlib snapshot.

A persistent local machine (or a GCE VM with a persistent disk) runs:

    LEAN_UPSTREAM=/path/to/openai-math \
    LEAN_CACHE_ROOT=/persistent/lean-eth \
    LEAN_BUILD_JOBS=2 \
      bash scripts/verify_lean_local.sh

If Mathlib was already restored from offline artifacts, add
`LEAN_SKIP_CACHE_GET=1`. The script verifies source revision, Lean and Lake
versions, Mathlib revision, and an architecture-keyed stable build directory.
The default `LEAN_TRACE_KIND=semantic` builds and executes the previously
verified **counting DFS** source definitions and compares 16 exact traces.
When the separate primitive driver is present, select `LEAN_TRACE_KIND=primitive`
to compile the normalization and terminal-leaf BitPrograms and compare their
physical outputs. Primitive mode is still an unverified acceptance obligation. The optional primitive driver has a finite 250,000-step/input budget.

Evidence lives in the persistent cache: build logs, native output, stderr,
Python comparator result, and SHA-256. A failed step cannot yield a certified
count. Repeating the command **reuses** existing Lake outputs instead of
rebuilding ~9,000 modules from a cold GitHub Actions runner.

A disposable ChatGPT VM does not persist the local build automatically.
Restore a checksum-pinned snapshot of the compiler, original source checkout,
Mathlib sources and the `.lake` directory at the **same absolute path**
from the file Library or private, generation-pinned GCS. A persistent GCE
build disk is usually preferable for large Lean dependency trees.

The expensive GitHub Actions workflow is **manual-only**, not triggered by
source pushes. GitHub remains the canonical source, PR and fast checkpoint.

Semantic mode checks finite CNF and counting-DFS correspondence, not
primitive execution. A passing primitive run would establish physical
execution for the normalizer and trivial terminal leaf only, not the
nonterminal marked-query loop or the worst-case complexity theorem.
