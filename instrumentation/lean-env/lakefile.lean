import Lake
open Lake DSL

-- Narrow, source-pinned reproduction of the original machine's dependencies.
-- The original OAI modules are linked from openai/math at the exact source pin.
package OAI where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target] lean_lib OAI
