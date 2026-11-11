# M2 outer machine: executable boundaries

Pinned Lean source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

| Executable Rust construction | Original source | Machine contract |
|---|---|---|
| `native_ambient::nat_program` | `ParserProgram.natProgram` (blob `9461361e12630b91419b6788ea8d2af4b2de5e9b`) | Exact five-label unary-field scanner, register 1 reports truncation |
| `native_ambient::ambient_command` | `Native.ambientCommand` (NativeFrontend.lean, blob `bdf989fb6a58332fe298ad157357ca684f6e1a41`) | 80×1220, copies 256→1218 preserving original, seeds/parses unary header to 258, clears work 1218 and copy scratch 1219 |
| `native_answer::zero_program` | `CounterPrograms.zeroProgram` (blob `5e22b28bfa71635b25b35a2e97295ec8705b678c`) | Ten-label exact counter-preserving binary zero test |
| `native_answer::answer_command` | `Native.answerCommand` (NativeProgram.lean, blob `864ccb2308317df3cc7d218c8b45d43d32558ffd`) | 80×1220, clears 1216 and 1217; scans all bits of count 256 using registers 72/73/74; writes a single Boolean to answer 1216 |

The ambient command assumes the *source's canonical input/empty-port premises*: header is `Encoding.encodeNat n ++ body`, and 258, 1218 and 1219 begin empty. Running it on arbitrary malformed input is not a validated parsing result. The low-level unary parser itself exposes the failure/presence bit, but the ambient composite subsequently clears its registers as prescribed by Lean. Full frontend validation, preprocessing and normalization are **not** implemented.

The answer suffix is independent of the missing count producer and is a real executable machine. It consumes a physical little-endian Boolean count word, not a host integer. `0b1000` (the LSB is zero) yields satisfiable, rather than checking only the LSB. It preserves the original noncanonical word and clears stale output/scratch. Source `Native.answerSteps a` predicts **exactly** `2*|oldAnswer| + 2*|oldScratch| + 8*|count| + 15` steps in the compiled machine.

## Tests and verification boundary

The Rust source snapshot was tested on pinned Rust 1.99.1 with offline cargo debug/release tests, strict Clippy and `cargo fmt --check`:

- Exact ten- and five-label instruction tables.
- Exhaustive binary count words (including leading zeroes), old dirty answer/scratch and full-word positivity.
- Exhaustive unary headers and four-bit trailing payloads.
- Physical stack/register preservation, completed halts and exact source instruction counts.
- Early instruction-budget refusal with no completed answer.

The standalone archive lacks the repository's `remaining.rs` registry. Its new stage wrappers were reviewed against the live GitHub branch but a **fresh exact-head combined-branch compile/CI check is still required**. No original imported Lean trace was executed. Source-table tests in Rust, while valuable, do not prove Lean/Rust observational refinement or TM2 resource bounds.

**Still unsupported:** `Native.frontendCommand`, `Native.setupAfterFrontend`, `DFSCountProgram.command`, `Native.outerCommand`, `Native.entryCommand` and `Native.countingProgram`. They still refuse in `remaining.rs`. These concrete endpoints supply two real integration seams for #107 after M1 query and M2 leaf/high-query work complete. The noncomputable finite fallback is handled separately in #108.
