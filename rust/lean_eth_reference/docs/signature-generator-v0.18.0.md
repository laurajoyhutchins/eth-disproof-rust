# v0.18.0: executable attained-signature generator initialization

Pinned Lean source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

New native code implements:

* `SqrtLogSpace.Counters.powerTwoProgram`, the seven-label consuming machine building the little-endian bit word for `2^h` from a length witness. The machine uses `4h+5` steps including halt.
* `SignatureTupleProgram.initialFuelCommand`, a lifted copy of that machine on registers `0..2` and tuple stacks `840`, `843`.
* `SignatureTupleProgram.resetCommand`, which copies the zero word at `651` to `838` and `840`, consumes the latter into binary fuel, and sets available/fresh to true/false.
* `SignatureTupleProgram.resetGeneratorCommand`, which additionally copies the source zero word into predecessor stack `844`.
* `SignatureTupleNative.setupWith loadHead`, which clears all twelve tuple stacks `836..847`, runs the existing initializer, then branches to `loadHead; resetGenerator` for nonempty head lists. Zero heads skip the loader and generator reset, retaining one leaf for the empty tuple.

All are source finite-machine commands. The head loader remains a **parameter** to `setupWith`; this does not assert that `SignatureTupleLoader.loadHead`, the predecessor rescan predicate, or `QueryVisitorProgram.visitor` is executable. The tests use a distinct finite sentinel loader to establish the branch behavior, not a replacement loader for query semantics.

The invariant for `resetCommand` is: stack `651` contains `h` zero bits; tuple scratch `841`, fuel output `843`, temporary `840`, and destination `838` are empty. The compiled-program instruction count is `18h+18`, which adds one final halt instruction to Lean's command evaluation cost `18h+17`. `resetGeneratorCommand` takes `25h+23` compiled instructions under the same preconditions.

Local verification on the standalone source snapshot: 135 tests in debug and release mode, `cargo fmt --check`, and `cargo clippy --all-targets --offline -- -D warnings` with Rust 1.99.1. The snapshot includes a local copy of the existing `native_signature_tuple::initialize_levels_command` from main for compilation; it is not a new upstream change. The full combined GitHub branch and Lean-import differential traces require separate verification.
