# Milestone 1: physical streamed-pair sign

Source pin: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`; `SqrtLogSpace/QueryProgram.lean` Git blob `7a2535f7c479463a5f5ed8a30a33192aad1b063e`.

The source `pairUpdate` begins with `pairSignCall`, followed by `signedAccumulate` and a physical pop of the sign cell. This increment implements **only** the first physical stage, without fabricating any scaled value.

`parityProgram` has four explicit instructions: pop, branch, XOR, halt. `pairSign` zeros register 2, preserving-copies E from local 0 to 2 through temporary 3, scans its parity, then preserving-copies and scans U, and pushes one final sign bit on local stack 2. The complete command is source-parametric in the two finite words and has constant-size instruction table; runtime steps scale with word length.

The source `pairRegisters : Fin 3 → Fin 40 := Fin.castAdd 37` uses **indices 0,1,2 without offset**. The stack embedding is `[834,835,848,849]`. Input masks 834/835 and all ambient query, tuple, dictionary, and accumulator words are preserved; result stack 848 contains `[sign]` and temporary 849 is empty. Scratch 848/849 must initially be empty. Actual downstream `pairUpdate` consumes the sign by a final pop.

Source `pairSignProgram` takes `10*(|E|+|U|)+19` compiled steps, and a compiled wrapper around `pairSignCall` takes one additional final halt step. Exhaustive tests independently compute parity from Boolean mask cardinality and, for `U ⊆ E`, verify the finite-difference sign `(-1)^(|E|-|U|)`. The machine never invokes an integer sign oracle.

## Evidence and limits


**Unfinished:** actual `signedAccumulate`, `QueryAssembler.pairUpdate` and `commitPair`, and production `SignatureTupleComplete.command`. The sign stage does not update accumulated count 850 and cannot be used as a complete pair callback.
