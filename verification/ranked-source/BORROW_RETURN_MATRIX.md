# Source-derived Vec borrow/return translation matrix

This is a **diagnostic**, not a second implementation of ranked counting. The
thirteen small functions in [borrow_return_probe.rs](src/borrow_return_probe.rs)
isolate the Aeneas translation failure at the real arithmetic-recorder
mutation/return boundary. They are compiled as a separate module by the
existing source-linked verification harness, alongside the **unmodified**
production ranked decoder, guard and traced executor.

The fourteenth extraction target, `ranked-source`, includes the **actual production
`execute_ranked_wire`** and must remain blocked unless *that* source closure
is translated. The synthetic probe results never certify it.

| Target | Mutable sink | Conditional sink | Arithmetic result | Ownership |
| --- | --- | --- | --- | --- |
| p0 | none | no | `Result<u64,u8>` | scalar |
| p1 | `&mut Vec<u64>` | no | fresh `Ok` | borrowed |
| p2 | `&mut Vec<u64>` | no | stored `Result` | borrowed |
| p3 | `&mut Option<&mut Vec<u64>>` | yes | fresh `Ok` | nested borrow |
| p4 | `&mut Option<&mut Vec<u64>>` | yes | stored `Result` | nested borrow |
| p5 | `&mut Vec<Option<i128>>` | no | stored checked `Result` | borrowed |
| p6 | `&mut Option<&mut Vec<Option<i128>>>` | yes | stored checked `Result` | nested borrow |
| p7 | owned `Vec<Option<i128>>` | no | stored checked `Result` | owned |
| p8 | none | no | checked `i128` result | scalar |
| p9 | `&mut Vec<Option<i128>>` | no | fresh `Ok` | borrowed |
| p10 | `&mut Vec<i128>` | no | stored checked `Result` | borrowed |
| p11 | `&mut Vec<Option<i128>>` | no | fresh `Ok` after checked addition | borrowed |
| p12 | `&mut Vec<Option<i128>>` | no | stored checked `Result` after appending the computed `Option` | borrowed |

**Two-phase diagnosis:** the first exact-head extraction [run #44807999037](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44807999037) translated p0–p2 with no local placeholders. Optional-nested-borrow p3/p4 failed as `Unimplemented`, while p5–p7 and the real source failed with partial `sorry` declarations. Even owned p7 failed, so neither a direct `Vec::push` nor returning a stored `Result` alone explains the recorder failure. The added p8–p11 cases distinguish whether the remaining failure needs checked-`i128`, option payloads, mutation, or their interaction. No synthetic case certifies actual production execution.

**Second-stage observation:** [exact-head workflow #44809224683](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44809224683) at `23a2080` successfully extracted **all four added controls**: p8 checked arithmetic without a vector, p9 option-valued vector push without arithmetic, p10 checked arithmetic with a scalar vector, and p11 computed-option vector recording with a fresh `Ok`. No local placeholders appeared in those four generated declarations. The unchanged p3/p4 remained `Unimplemented`, p5/p6/p7 remained interpreter errors with `sorry`, and production `ranked-source` remained blocked.

Thus neither checked-`i128` arithmetic, option-valued vectors, checked-result return, nor their **separately tested simpler combinations** explain the remaining interpreter error. The final one-factor contrast p12 records `left.checked_add(right)` directly and converts it to a returned `Result` **after** the vector effect; deterministic Rust tests compare its result and recorded vector to p5 on both successful and overflowing inputs. Its source-derived translation and universal equivalence to p5 are **not** inferred from those tests. The key additional contrast is p11 versus p5: p11 records the checked `Option` but returns a **fresh** `Ok`; p5 records `outcome.as_ref().ok().copied()` and then returns the **stored** `Result`. This implicates their precise interaction, not a mathematically invalid arithmetic operation. The observation does **not** prove a unique symbolic-execution root cause.

The generated `ProbeP2` Lean 4.31.0 project built successfully, but the first independent post-state theorem check stopped at a Lean **import-order syntax error** before its proof was elaborated. Its status is **unproved**, pending the corrected exact-head kernel check. This failed proof check is distinct from the successful package build and should never be reported as a theorem.

The [change-scoped matrix workflow](../../.github/workflows/ranked-borrow-matrix.yml)
runs the Rust behavioral tests and each scenario in the pinned hax 0.4.2
backend separately. It retains **both passing and failing** full extraction
logs, actual generated Lean files, LLBC and a tabular status summary.

A successful scenario requires all three independently observed properties:
hax exits successfully, the requested original declaration is present in
generated `Funs.lean`, and generated local `Funs.lean`/`Types.lean` contain
no obvious `sorry`/`admit`/`axiom`/`sorryAx` tokens. A run containing
translation failures stays **red**, not magically green because failures
were expected. A failure to produce `Funs.lean` is reported as missing,
not as a clean source translation.

A separate [Lean proof candidate](proofs/BorrowReturnP2.lean) is copied into
the **actual** generated `ProbeP2` package and typechecked by Lean 4.31.0.
The theorem states that if the Aeneas `Vec.push` model succeeds with
`events'`, the extracted `p2_direct_result` returns the independently
specified `Result` and the exact `events'` post-state. This is a scoped,
conditional source-derived theorem and is *not* a model of allocation
failure, actual CPU/Rust semantics, or the full ranked production recorder.
The conditional P2 post-state theorem **was kernel-checked** at exact head `a0c29a2` in [run #44872606629](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44872606629). The proof axiom report lists standard Lean axioms and no `sorryAx`. This is a model-level theorem about genuine generated p2, not a production Rust refinement.

The [new P12 proof candidate](proofs/BorrowReturnP12.lean) imports
`ProbeP12.Extraction.Funs`, the genuine Aeneas source-derived checked
recorder. It states the ordered post-state under successful modelled checked
addition and vector push, then specializes to both `Some value` success
and `None` overflow refusal, preserving an event in both cases. The
[change-scoped workflow](../../.github/workflows/ranked-borrow-matrix.yml)
checks it with the pinned generated Lean 4.31.0 project and rejects
`sorryAx` dependencies. Until that **exact-head step passes**, it remains
an unverified proof candidate. Even a passing theorem does not independently
verify `IScalar.overflowing_add` against CPU behavior.

The arithmetic-model boundary is explicit in pinned
[CoreModels `num.I128.checked_add`](https://github.com/cryspen/hax-lean/blob/v0.3.30/CoreModels/Core/Funs.lean):
it calls `num.I128.overflowing_add`, and maps an overflow flag to
`Option.None`. The pinned primitive model in
[`CoreModels/RustPrimitives/Funs.lean`](https://github.com/cryspen/hax-lean/blob/v0.3.30/CoreModels/RustPrimitives/Funs.lean)
uses `IScalar.overflowing_add`. The independent
[`ACC.CheckedI128BitVec.checkedWordAdd_eq_checkedAdd`](../../instrumentation/lean-env/ACC/CheckedI128BitVec.lean)
establishes a different Lean 4.34.1 BitVec/integer model. A complete
cross-model theorem and source-to-machine implementation argument remain
unproved.

Even a green row is **only source-extraction evidence**. No row establishes
Lean kernel typechecking, absence of placeholders in transitive dependencies,
soundness of library or allocation models, or semantic equivalence to Rust.
Those require their own verified theorems on the **actual extracted source**,
rather than a handwritten Lean approximation.

Run the fast behavior checks from the repository root:

```sh
cargo fmt --all -- --check
cargo test --locked -p ranked-source-proof-harness --lib
cargo clippy --locked -p ranked-source-proof-harness --all-targets -- -D warnings
```

For one experiment use `cd verification/ranked-source && cargo hax extract
probe-p5 --locked` with pinned hax 0.4.2. The original full source extraction
remains in the separate ranked extraction workflow and draft #408.

The practical objective is **localization**: distinguish whether the
translator fails on direct `Vec::push`, branching over an optional
borrow, returning a stored `Result`, or the checked-`i128` library model.
Only after a clear boundary is found should production Rust be redesigned
or a formal source-level refinement proof attempted.
