import NativeRust
import Library

namespace Closure
  def pipeline (x : UInt64) : UInt64 := Library.left x + Library.right x

  partial def descend (x : UInt64) : UInt64 :=
    if x == 0 then 7 else descend (x - 1)

  mutual
    partial def isEven (x : UInt64) : UInt64 :=
      if x == 0 then 1 else isOdd (x - 1)
    partial def isOdd (x : UInt64) : UInt64 :=
      if x == 0 then 0 else isEven (x - 1)
  end
end Closure

#native_rust_closure Closure.pipeline as "pipeline" to "examples/generated_closure.rs"
#native_rust_closure Closure.descend as "descend" to "examples/generated_descend.rs"
#native_rust_closure Closure.isEven as "is_even" to "examples/generated_mutual.rs"

open Lean Elab Command
-- Lean itself computes the expected values; none are provided to the backend.
run_cmd do
  let mut content := "{\n"
  let mut state : UInt64 := 0xD1B54A32D192ED03
  let edges : Array UInt64 := #[0, 1, 2, 3, 7, 42, UInt64.ofNat (2^32-1),
                                UInt64.ofNat (2^63), UInt64.ofNat (2^64-1)]
  for idx in [:128] do
    if idx < edges.size then
      state := edges[idx]!
    else
      state := state * 6364136223846793005 + 1442695040888963407
    let small := UInt64.ofNat (idx % 32)
    let n := state.toNat
    content := content ++ s!"    assert_eq!(pipeline({n}u64), {(Closure.pipeline state).toNat}u64);\n"
    content := content ++ s!"    assert_eq!(descend({small.toNat}u64), {(Closure.descend small).toNat}u64);\n"
    content := content ++ s!"    assert_eq!(is_even({small.toNat}u64), {(Closure.isEven small).toNat}u64);\n"
  content := content ++ "}\n"
  liftIO <| IO.FS.writeFile "examples/generated_closure_differential.rs" content
  logInfo "Generated 384 independently evaluated closure/recursion assertions"
