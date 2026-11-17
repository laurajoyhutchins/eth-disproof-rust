import NativeRust
open Lean Elab Command

namespace FunctionValues
  @[noinline] def plus (a b : UInt64) : UInt64 := a + b
  @[noinline] def times (a b : UInt64) : UInt64 := a * b

  -- This external-looking boundary is still ordinary source-defined Lean.
  -- IR uses boxed AP rather than specializing away the function value.
  @[noinline] def applyValue (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f x

  def runIndirect (flag : Bool) (x y : UInt64) : UInt64 :=
    applyValue (if flag then plus x else times x) y

  @[noinline] def pack (flag : Bool) (x : UInt64) : Option (UInt64 → UInt64) :=
    if x < 8 then none else some (if flag then plus x else times x)

  def runPacked (flag : Bool) (x y : UInt64) : UInt64 :=
    match pack flag x with
    | none => 19
    | some f => f y

  def runShared (flag : Bool) (x y z : UInt64) : UInt64 :=
    let f := if flag then plus x else times x
    applyValue f y + applyValue f z

  @[noinline] def applyTwo (f : UInt64 → UInt64 → UInt64) (y z : UInt64) : UInt64 :=
    let half := f y
    half z

  def runMulti (flag : Bool) (x y z : UInt64) : UInt64 :=
    let f : UInt64 → UInt64 → UInt64 :=
      if flag then (fun a b => x + a + b) else (fun a b => x * a + b)
    applyTwo f y z
end FunctionValues

#native_rust_package [FunctionValues.runIndirect, FunctionValues.runPacked, FunctionValues.runShared, FunctionValues.runMulti] to "examples/function-package"

run_cmd do
  let mut text := "use lean_generated::{runIndirect, runPacked, runShared, runMulti};\n#[test] fn closure_differential() {\n"
  let mut state : UInt64 := 14029467366897019727
  for i in [:512] do
    state := state * 2862933555777941757 + 3037000493
    let flag := i % 2 == 0
    let x : UInt64 := if i % 11 == 0 then UInt64.ofNat (i % 16) else state
    let y : UInt64 := state * 6364136223846793005 + 7
    let z : UInt64 := state + 1
    let b := if flag then 1 else 0
    text := text ++ s!"assert_eq!(runIndirect({b}u8,{x.toNat}u64,{y.toNat}u64),{(FunctionValues.runIndirect flag x y).toNat}u64);\n"
    text := text ++ s!"assert_eq!(runPacked({b}u8,{x.toNat}u64,{y.toNat}u64),{(FunctionValues.runPacked flag x y).toNat}u64);\n"
    text := text ++ s!"assert_eq!(runShared({b}u8,{x.toNat}u64,{y.toNat}u64,{z.toNat}u64),{(FunctionValues.runShared flag x y z).toNat}u64);\n"
    text := text ++ s!"assert_eq!(runMulti({b}u8,{x.toNat}u64,{y.toNat}u64,{z.toNat}u64),{(FunctionValues.runMulti flag x y z).toNat}u64);\n"
  text := text ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/function-package/tests"
  liftIO <| IO.FS.writeFile "examples/function-package/tests/closures.rs" text
  logInfo "Generated 2048 original-Lean function value and indirect AP differential assertions"
