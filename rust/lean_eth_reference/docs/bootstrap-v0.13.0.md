# Complete native bootstrap, v0.13.0

Source pin: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
`SqrtLogSpace/SignatureHeadLoader.lean`,
`SqrtLog/LeafHeadSetupProgramBoot.lean`,
`SqrtLog/LeafHeadSetupProgramStorage.lean`, and
`SqrtLog/LeafHeadSetupProgramRetain.lean`.

Executable finite command: `bootstrap_program()` is the compilation of
`initializeAddress ;; countRows ;; initializeCache ;; retainCache`,
with input port 307 and output port 647. The three services run in the
physically isolated 340..627 work region with temporary port 659.
The integer-cache stage uses 340..363, reads protected source ports
139/138/140 into 20/21/22, and emits 640/641/642/643. Preserving copies
append those first three outputs into 710/711/712. The node-level callback
lifts the complete 16×768 program to 40×896 at register offset 24
and stack offset 128.

Tests execute real machine steps, assert coefficient values and serialized
denominator, check preserved tails, verify dirty work-bank cleanup,
compare staged composition to four separately run compiled programs,
compare all 768 lowered stacks and 16 registers against the lifted node
callback, and demand explicit refusal on instruction-limit exhaustion.

The Lean theorem for coefficient values requires runtime width
W >= 1 + 2*A*R. The machine does not enforce this assumption.
No imported-source Lean/Rust trace comparison has been performed.
The query body, pair expansion, node finish, and final solver are still
unimplemented and must remain fail-closed.
