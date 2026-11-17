import CompilerConfig

/-! Independent oracle from official, pinned Lean. -/

private def flag (b : Bool) : String := if b then "1" else "0"

def main : IO Unit := do
  for idx in [:256] do
    let tag := UInt8.ofNat idx
    IO.println s!"{idx}\t{flag (CompilerConfig.probe_eta tag)}\t{flag (CompilerConfig.probe_inline_partial tag)}\t{flag (CompilerConfig.probe_implemented_by tag)}\t{flag (CompilerConfig.probe_inline_defs tag)}"
