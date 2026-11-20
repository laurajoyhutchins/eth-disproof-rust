# Source-derived Vec borrow/return translation matrix

This is a **diagnostic**, not a second implementation of ranked counting. The
twelve small functions in [borrow_return_probe.rs](src/borrow_return_probe.rs)
isolate the Aeneas translation failure at the real arithmetic-recorder
mutation/return boundary. They are compiled as a separate module by the
existing source-linked verification harness, alongside the **unmodified**
production ranked decoder, guard and traced executor.

The thirteenth extraction target, `ranked-source`, includes the **actual production
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

**Two-phase diagnosis:** the first exact-head extraction [run #44807999037](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44807999037) translated p0–p2 with no local placeholders. Optional-nested-borrow p3/p4 failed as `Unimplemented`, while p5–p7 and the real source failed with partial `sorry` declarations. Even owned p7 failed, so neither a direct `Vec::push` nor returning a stored `Result` alone explains the recorder failure. The added p8–p11 cases distinguish whether the remaining failure needs checked-`i128`, option payloads, mutation, or their interaction. No synthetic case certifies actual production execution.

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
Its kernel verdict must be checked on the exact head before reporting it
as proved.

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
