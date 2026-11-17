import NativeRust
open Lean Elab Command

namespace ArrayFixture
  def appendAndRead (x y : UInt64) : UInt64 :=
    let a : Array UInt64 := #[x]
    let a := a.push y
    a.getD 0 0 + a.getD 1 0

  def updatePreservesOld (x y : UInt64) : UInt64 :=
    let a : Array UInt64 := #[x, y]
    let b := a.set! 0 (x + 1)
    b.getD 0 0 + a.getD 0 0

  def chooseBySize (x y : UInt64) : UInt64 :=
    let a := (#[x] : Array UInt64).push y
    if a.size == 2 then a.getD 1 0 else x
  def emptyDefault (x : UInt64) : UInt64 :=
    let a : Array UInt64 := if x == 0 then #[] else #[x]
    a.getD 3 x

  def nestedSome (x y : UInt64) : UInt64 :=
    let a : Array UInt64 := #[x]
    let wrapped : Option (Array UInt64) := some a
    match wrapped with
    | none => 19
    | some b => (b.push y).getD 1 0 + a.getD 0 0
end ArrayFixture

#native_rust_package [ArrayFixture.appendAndRead, ArrayFixture.updatePreservesOld, ArrayFixture.chooseBySize, ArrayFixture.emptyDefault, ArrayFixture.nestedSome]
  to "examples/array-package"

run_cmd do
  let mut text := "use lean_generated::*;\n#[test] fn array_differential() {\n"
  let mut state : UInt64 := 1789321321
  for i in [:256] do
    state := state * 6364136223846793005 + 1442695040888963407
    let x : UInt64 := if i < 5 then UInt64.ofNat i else state
    let y : UInt64 := if i < 5 then UInt64.ofNat (4 - i) else (state + 1)
    text := text ++ s!"assert_eq!(appendAndRead({x.toNat}u64, {y.toNat}u64), {(ArrayFixture.appendAndRead x y).toNat}u64);\n"
    text := text ++ s!"assert_eq!(updatePreservesOld({x.toNat}u64, {y.toNat}u64), {(ArrayFixture.updatePreservesOld x y).toNat}u64);\n"
    text := text ++ s!"assert_eq!(emptyDefault({x.toNat}u64), {(ArrayFixture.emptyDefault x).toNat}u64);\n"
    text := text ++ s!"assert_eq!(nestedSome({x.toNat}u64, {y.toNat}u64), {(ArrayFixture.nestedSome x y).toNat}u64);\n"
    text := text ++ s!"assert_eq!(chooseBySize({x.toNat}u64, {y.toNat}u64), {(ArrayFixture.chooseBySize x y).toNat}u64);\n"
  text := text ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/array-package/tests"
  liftIO <| IO.FS.writeFile "examples/array-package/tests/arrays.rs" text
  logInfo "Generated 1280 Lean-evaluated Array differential assertions"
