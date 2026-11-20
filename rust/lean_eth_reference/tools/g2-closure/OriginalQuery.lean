/-!
Actual pinned source prerequisite:
openai/math@4eaee87548250b2682affda7d05d947c05554bae
Lean 4.34.1 with the committed Mathlib/Lake lock.

Only run after the original imported module is built and source provenance
is verified. The resulting inventory is *not* an executable Rust program.
-/
import G2Inventory
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram

#eth_closure_inventory OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.program
