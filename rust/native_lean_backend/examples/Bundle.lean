import NativeRust
import Library

namespace Bundle
  def first (x : UInt64) : UInt64 := Library.left x + Library.right x
  def second (x : UInt64) : UInt64 := Library.bump (Library.triple x)
end Bundle

#native_rust_bundle [Bundle.first, Bundle.second]
  as ["first", "second"] to "examples/generated_bundle.rs"

open Lean Elab Command
run_cmd do
  let mut lines := "use generated_bundle::{first, second};\n#[test]\nfn differential_bundle() {\n"
  let mut state : UInt64 := 0xD1B54A32D192ED03
  let edges : Array UInt64 := #[0, 1, 2, 3, 7, 42, UInt64.ofNat (2^32-1),
                                UInt64.ofNat (2^63), UInt64.ofNat (2^64-1)]
  for index in [:128] do
    if index < edges.size then
      state := edges[index]!
    else
      state := state * 6364136223846793005 + 1442695040888963407
    let n := state.toNat
    lines := lines ++ s!"    assert_eq!(first({n}u64), {(Bundle.first state).toNat}u64);\n"
    lines := lines ++ s!"    assert_eq!(second({n}u64), {(Bundle.second state).toNat}u64);\n"
  lines := lines ++ "}\n"
  liftIO <| IO.FS.writeFile "examples/generated_bundle_differential.rs" lines
  logInfo "Generated 256 independently Lean-evaluated multi-root assertions"
