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
cd rust/native_lean_backend
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

## What remains unanswered

1. **Diverse original programs:** benchmark source-matched closures, arrays,
   GMP-backed `Nat`, and original external projects. A recursive `UInt64`
   function is not a representative distribution of Lean code.
2. **Steady-state runtime:** separate process startup from compute time and
   report statistical uncertainty across isolated/repeated environments.
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
