import Lake
open Lake DSL

-- The sole external package is the exact Mathlib revision required by OpenAI.
-- CI symlinks OAI to a clean checkout of the pinned original source.
package OAI where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target] lean_lib OAI
