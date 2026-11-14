import NativeRust
open Lean Elab Command

namespace ObjectFixture
  def mkOpt (x : UInt64) : Option UInt64 :=
    if x < 8 then some (x + 1) else none
  def getOpt (x : Option UInt64) : UInt64 :=
    match x with
    | .none => 2
    | .some n => n + 7
  def optionRoundTrip (x : UInt64) : UInt64 := getOpt (mkOpt x)

  def mkPair (x : UInt64) : UInt64 × UInt64 := (x, x + 1)
  def consumePair (p : UInt64 × UInt64) : UInt64 := p.1 + p.2
  def pairRoundTrip (x : UInt64) : UInt64 := consumePair (mkPair x)

  def nested (x : UInt64) : UInt64 :=
    let inner : Option UInt64 := if x < 8 then some x else none
    let outer : Option (Option UInt64) := some inner
    match outer with
    | none => 17
    | some none => 19
    | some (some n) => n + 2
end ObjectFixture

#native_rust_package [ObjectFixture.optionRoundTrip, ObjectFixture.pairRoundTrip, ObjectFixture.nested] to "examples/object-package"

run_cmd do
  let mut text := String.join [
    "use lean_generated::{optionRoundTrip, pairRoundTrip, nested};\n",
    "#[test] fn object_differential() {\n"
  ]
  let mut state : UInt64 := 179424691
  for i in [:1024] do
    state := state * 2862933555777941757 + 3037000493
    let x := if i < 8 then UInt64.ofNat i else if i < 16 then UInt64.ofNat (i-8) + UInt64.ofNat (2^64 - 8) else state
    text := text ++ s!"assert_eq!(optionRoundTrip({x.toNat}u64), {(ObjectFixture.optionRoundTrip x).toNat}u64);\n"
    text := text ++ s!"assert_eq!(pairRoundTrip({x.toNat}u64), {(ObjectFixture.pairRoundTrip x).toNat}u64);\n"
    text := text ++ s!"assert_eq!(nested({x.toNat}u64), {(ObjectFixture.nested x).toNat}u64);\n"
  text := text ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/object-package/tests"
  liftIO <| IO.FS.writeFile "examples/object-package/tests/objects.rs" text
  logInfo "Generated 3072 Lean-evaluated constructor/object differential assertions"
