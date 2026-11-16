import Bootstrap

/-!
Run by official pinned Lean, not by the new Rust code generator. Its output
is a tab-separated independent oracle over every UInt8 tag.
-/

private def flag (b : Bool) : String := if b then "1" else "0"

def main : IO Unit := do
  for idx in [:256] do
    let tag := UInt8.ofNat idx
    IO.println s!"{idx}\t{flag (Bootstrap.probe_scalar tag)}\t{flag (Bootstrap.probe_object tag)}\t{flag (Bootstrap.probe_possible_ref tag)}\t{flag (Bootstrap.probe_definite_ref tag)}\t{flag (Bootstrap.probe_erased tag)}\t{flag (Bootstrap.probe_boxed_tagged tag)}"
