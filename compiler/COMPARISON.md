# Lean's C backend versus the in-process Rust backend

This is a **paired, exact-source execution comparison**. It is not a claim that
Rust is generally faster or that the compiler has passed G1/G2 acceptance.

## The program

Both outputs execute the original `Property.hop` in
[`examples/PropertyDef.lean`](examples/PropertyDef.lean), a bounded recursive
`UInt64` function. Lean 4.34.1 compiles that declaration into its own C output.
Our compiler consumes the **live `Lean.IR.Decl` of that same definition** through
the in-process FFI, then emits Rust.

The C driver is [`examples/PropertyNativeBenchmark.lean`](examples/PropertyNativeBenchmark.lean)
and is also compiled by Lean to C. The Rust driver
[`examples/property_native_benchmark.rs`](examples/property_native_benchmark.rs)
contains a matching deterministic input generator and includes the emitted
Rust implementation, rather than reimplementing `Property.hop`.
The original Lean interpreter is the third producer of the checksum.

All three process **1,048,576** deterministic inputs. The expected output is
`1595490202785243536`, with an exact byte-for-byte comparison of stdout.
The tests fail if any compiler changes behavior.

## Verified baseline (November 14, 2026)

- Compiler revision: [`863dbf9cec2e3cd6804cc56837c0cb97bfbdb479`](https://github.com/laurajoyhutchins/eth-disproof-rust/commit/863dbf9cec2e3cd6804cc56837c0cb97bfbdb479)
- [Exact-head native CI run 43659172043](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43659172043)
- Lean: **4.34.1** (`5045d005`); Rust: **1.99.1** (`58cf8f9c3`)
- Both binaries passed original Lean / Lean C / emitted Rust stdout parity.

| Measured quantity | Lean C | Emitted Rust |
| --- | ---: | ---: |
| Median subprocess elapsed, 30 alternating trials | 22,529,051 ns | 4,669,287 ns |
| Three peak RSS samples (KiB) | 9384 / 9388 / 9444 | 2256 / 2280 / 2020 |
| Independently checked output | `1595490202785243536` | `1595490202785243536` |
| Lean runtime linked by generated executable | Yes | No |

**Observed ratio**: 4.83× lower median subprocess time for Rust in *this* sample.
This includes launch/exit overhead. The GitHub runner is not isolated, and the
sample covers only a scalar recursive function, not arrays, GMP, closures, or
general Lean programs. Do not extrapolate the ratio to other workloads.

## First compiled-pipeline measurement (PR #249)

[Exact-head CI run 43660083941](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43660083941)
passed at commit `64ac3afdd89149abc574bb219be4a22282e91405` on a
four-CPU Ubuntu 24.04 hosted runner with clang 22.1.4. All freshly compiled
binaries reproduced the original Lean checksum, and the generated Rust source
was identical across three runs.

| Median phase, three observations | Lean → C | Lean IR → Rust |
| --- | ---: | ---: |
| Compile original definition to C or `.olean` | 0.20 s | 0.21 s |
| Compile Lean-language benchmark driver to C | 0.20 s | Not applicable |
| Load already-compiled IR and emit Rust | Not applicable | 0.67 s |
| Compile and link executable | 0.39 s | 0.07 s |
| Largest observed peak RSS in codegen/preparation | ~494 MiB | ~1,575 MiB |
| Unstripped executable byte size | 4,478,928 | 4,537,472 |

The corresponding runtime medians were **29,235,601 ns (C)** and
**6,935,221 ns (Rust)**, a **4.22×** observed difference; runtime RSS samples
were **9,232–9,408 KiB** for C and **2,152 KiB** for Rust.

The phase totals are not a controlled apples-to-apples compiler benchmark:
one path emits C from source; the other consumes imported `.olean` and loads
a plugin. In particular, the 0.67-second / ~1.54-GiB Rust emission process
may be dominated by Lean import/startup costs. The **import-control** phase in `compare-c-rust.sh` measures those same
imports and plugin loading without generating Rust. On [exact-head CI run
43660472757](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43660472757)
(commit `6631dc85d486580653ae41d1151adb66355f5356`), the import-only control
was **0.50 s median and 1,611,232–1,611,352 KiB peak RSS**, while the IR
emission command was **0.50 s median and 1,612,328–1,612,524 KiB peak RSS**.
The measured difference is near the timer resolution: **the enormous
in-process memory footprint is overwhelmingly present before Rust emission**.
That is evidence of a Lean import/plugin-startup cost, not evidence of an
intrinsically memory-hungry Rust IR translator. A controlled incremental
allocation profiler is still required for precise attribution.
The C and Rust native build optimizations are also not identical:
`leanc -O2` versus `rustc -O` (Rust optimization level 3).
On the same final run, the 30-trial runtime medians were **21.6241 ms C**
and **4.465482 ms Rust**, about **4.84×** in favor of Rust. The three-run
build-phase medians were: C source-to-C 0.15 s, driver-to-C 0.14 s and
C compile/link 0.29 s; Rust source-to-olean 0.16 s, import-only control
0.50 s (not additive), IR emission 0.50 s and Rust compile/link 0.06 s.
These remain phase measurements, not an equal-work compiler speedup.

The two executable files are of similar size, but C's Lean runtime is
dynamically linked and therefore excluded from its on-disk ELF size.

## Reproduce and extend the comparison

Use Linux x86-64, the exact pinned Lean distribution with headers and
libraries, Rust 1.99.1, GMP development libraries, a C toolchain and
`/usr/bin/time`. Run from the repository root:

```sh
cd compiler
export LEAN_PREFIX=/absolute/path/to/lean-4.34.1
lake build
./scripts/check.sh
bash ./scripts/check-native-runtime-parity.sh
bash ./scripts/compare-c-rust.sh
```

The first parity script generates and checks two binaries, then performs
**30 alternating-order, checksum-checked subprocess trials per backend**. It
writes:

- `artifacts/parity-native/measurements-ns.tsv` (raw runtime samples)
- `artifacts/parity-native/summary-ns.txt` (medians and timing scope)
- `artifacts/parity-native/receipt.txt` (source/toolchain hashes and semantics)

The additional `compare-c-rust.sh` repeats the build sequence three times
with alternating backend order, verifies each compiled binary against the
original Lean interpreter, and records:

- `artifacts/compare-native/compile-phases.tsv`: elapsed and peak RSS by phase
- `artifacts/compare-native/executables.tsv`: unstripped ELF byte size and hash
- `artifacts/compare-native/*-dynamic-dependencies.txt`: `ldd` resolution
- `artifacts/compare-native/receipt.txt`: input and generated hashes, toolchains,
  host details and limitations
- `artifacts/compare-native/*.log`: raw build outputs

The original `Property.hop` is unchanged. The emitted Rust is checked for
deterministic bytes across the repeated compilations.

## What the compile-phase measurements mean

| Backend | Phase | Includes |
| --- | --- | --- |
| Lean C | `source-to-c` | Lean frontend plus C emission for `PropertyDef` |
| Lean C | `driver-to-c` | Lean frontend plus C emission for the Lean driver |
| Lean C | `c-compile-and-link` | `leanc -O2` for the two generated C files |
| Lean Rust | `source-to-olean` | Lean frontend compilation of `PropertyDef` |
| Lean Rust | `import-control` | Lean startup, exactly the same module imports and plugin load, **without** code generation; control, not additive pipeline phase |
| Lean Rust | `in-process-ir-to-rust` | Lean startup, imported precompiled IR, FFI/backend Rust generation |
| Lean Rust | `rust-compile-and-link` | `rustc -O` of generated implementation plus Rust driver |

These are **phase observations**, not equal work units. For instance, the
Rust codegen process imports an already compiled `.olean`, while
`lean -c` includes frontend work. Rust generation also incurs plugin
loading. Summing phases answers a useful whole-build question for the
two demonstrated commands, but it cannot isolate the cost of IR lowering
without a shared frontend, warmup policy and separate link-stage experiments.

The binary size table reports *only the ELF files*, not the transitive size of
Lean's shared runtime, GMP, glibc, or other dynamic dependencies. Compare
`ldd` results before interpreting sizes. Peak RSS is per process, **not
peak memory across concurrent build or transitive shared-library usage**.
All compilation measurements are fresh-process but cache-uncontrolled,
with three observations rather than a statistically controlled benchmark.

## Representative workload matrix

The original comparison used only `Property.hop`, a fixed-width recursive
`UInt64` function. To make its limitations testable, the representative benchmark
compiles **four original Lean roots** in
[`examples/BenchmarkKernels.lean`](examples/BenchmarkKernels.lean) through
both compiler backends. No root is implemented a second time in Rust.

| Workload | Original Lean function(s) | What it exercises |
| --- | --- | --- |
| `array` | `BenchmarkKernels.arrayStep` | Persistent Array allocation, `set!`, `push`, and old-alias preservation |
| `closure` | `BenchmarkKernels.closureStep` | Indirect calls, partially applied function values and capture |
| `nat` | `BenchmarkKernels.natStep`, `natAccumulate` | GMP-backed 256-bit/128-bit multiplication, division, remainder, accumulation |

Each backend builds against *exactly the same* `BenchmarkKernels.lean`.
The native Lean driver is also source-compiled through Lean's C backend;
the Rust driver contains only deterministic inputs, accumulation, and
printing, and links the generated Rust Cargo library. These language-specific
drivers are a confound for total runtime; they are **not** replacement
implementations of the measured Lean roots.

The gate requires three-way parity against the original Lean interpreter at
32 iterations per workload, then native Lean C/Rust parity at 262,144 iterations
for arrays and closures and 12,000 iterations for Nat. Both binaries emit
an identical numeric checksum per workload. Twelve alternating subprocess
measurements per backend are taken after warmup, plus twelve zero-iteration
startup-only control samples per workload and backend. The runner also records
per-executable peak RSS, raw compiler phase timings, `ldd` dependencies,
emitted C and generated Rust source hashes, and source/toolchain identity.

Reproduce after `lake build` and `scripts/check.sh`:

```sh
bash scripts/compare-c-rust-matrix.sh
cat artifacts/bench-matrix/parity.tsv
cat artifacts/bench-matrix/compile-phases.tsv
cat artifacts/bench-matrix/{array,closure,nat}-summary.txt
cat artifacts/bench-matrix/{array,closure,nat}-startup-summary.txt
```

The native CI workflow executes this test after the existing `Property.hop`
comparison. Its evidence is archived at
`artifacts/bench-matrix/`. Failures are never represented as a speedup.

### Verified matrix baseline and the resulting compiler questions

[Native CI run 43699833669](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43699833669)
at commit `5fec979040e953d7f40783b4637a7649ebde18c0` passed
all interpreter/C/Rust parity gates, original external-project regression, and
the root Rust workspace. The workload medians below were calculated from the
**twelve archived raw nanosecond observations per backend**. They use the
conventional midpoint of the two center values; the first version of the
subprocess harness printed the upper center sample instead, which was close
but was not the mathematical median. The harness has since been corrected.

| Workload and calls | Lean native C median | Emitted Rust median | Observed difference |
| --- | ---: | ---: | --- |
| Array, 262,144 | 31.033 ms | 246.826 ms | Rust **7.95× slower** |
| Closures, 262,144 | 29.330 ms | 72.106 ms | Rust **2.46× slower** |
| GMP Nat, 12,000 | 16.047 ms | 6.909 ms | Rust **2.32× faster** |

Array execution peak RSS in the three tracked samples was
9,192–9,336 KiB for C and 2,672–2,792 KiB for Rust. Closure C RSS
was 9,332–9,404 KiB versus Rust 2,404–2,560 KiB. Nat C RSS was
8,944–8,976 KiB versus Rust 2,620–2,672 KiB. These are process-specific
measurements; shared runtime costs and platform differences are not normalized.

The one-sample build phases were 0.20 s to compile the Lean source to
`.olean`, 0.66 s to load Lean and emit Rust, and 0.48 s to compile/link the
generated Cargo executable. The C counterpart took 0.20 s for the source
module, 0.23 s for its driver module, and 0.52 s to compile/link. These
phases are **not equivalent**: Lean's frontend and source imports are charged
differently. No broad compiler-throughput ratio follows.

These results contradict the suggestion that the scalar-recursion speedup
automatically transfers to collections and closures. The C backend wins
substantially on the tested heap-backed programs.

**Concrete generated-code observation.** In the array program, the IR-derived
Rust currently emits `x_13.clone().array_push(&x_15.clone())` after
`array_set_tagged`. The emitted C executes `lean_array_push(v_b_13_, ...)`,
consuming that updated array. Rust has a specialized
`array_push_owned` runtime operation, but the conservative emitter's last-use
analysis did not select it in this join-point/control-flow case. This is a
specific, source-grounded performance opportunity, not an assertion that all
of the difference comes from that one copy. The closure path separately
allocates an Rc-backed PAP and clones captures before indirect application.
A correctness-preserving escape/last-use analysis could reduce this overhead,
but sharing and `isShared` behavior require careful semantic checks.

The follow-on zero-iteration trials explicitly measure process startup
without invoking any of the benchmark roots. Subtracting median startup
times from median full-run times can be a useful diagnostic, but must not
be reported as a precise compute-only benchmark without controlling noise,
input generation and backend driver costs.

### Unchanged external projects

The existing three-project acceptance matrix compiles **original Armada
`Sched.argLeastLoad`** and **Keboola `SyncModel.pullDecide`** into
standalone Rust and checks source-Lean results. **Newspeak is still an
explicit refusal** for the selected original root.

These are semantic compiler acceptance tests, **not currently equivalent C
versus Rust performance benchmarks**. A fair external benchmark needs an
unchanged source-compiled C executable and the same runtime inputs, not merely
the external Lean interpreter or a rewritten proxy. Until then its speed ratio
is `NOT_MEASURED`. No figure from the synthetic workload matrix should
be projected onto Armada, Keboola, or Newspeak.

## What remains unanswered

1. **Diverse original programs:** reproduce these synthetic source-matched
   results across original external projects, representative data sizes and
   workloads with different allocation/lifetime patterns. Newspeak still
   refuses for the selected root.
2. **Steady-state runtime:** use the zero-iteration startup control to
   distinguish launch cost from compute-dominated cost; then add in-process
   loop timing and uncertainty intervals on controlled hardware.
3. **Shared-phase compiler costs:** compare equal frontend and IR preparation,
   measure code generation separately from native compilation and linking,
   and examine cold/warm cache behavior.
4. **Semantic preservation:** finite checksum parity is not a proof of general
   Lean C / Rust semantic equivalence, especially around ownership,
   reference counts, mutation and effects.
5. **Cost model:** Lean's normal C output retains its Lean runtime. A Rust
   executable with no Lean runtime and a different allocation/representation
   model cannot be claimed to win generally from one favorable kernel.

The purpose of these receipts is to make subsequent performance work
inspectable and reproducible without confusing a narrow measurement for a
compiler-completion certificate.
