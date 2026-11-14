import Lean
open Lean Elab Command

namespace FunctionProbe
  @[noinline] def plus (a b : UInt64) : UInt64 := a + b
  @[noinline] def times (a b : UInt64) : UInt64 := a * b

  @[noinline] def choose (flag : Bool) (x : UInt64) : UInt64 → UInt64 :=
    if flag then plus x else times x

  def run (flag : Bool) (x y : UInt64) : UInt64 :=
    (choose flag x) y

  def runDirect (flag : Bool) (x y : UInt64) : UInt64 :=
    (if flag then plus x else times x) y
  @[noinline] def applyValue (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f x

  def runIndirect (flag : Bool) (x y : UInt64) : UInt64 :=
    applyValue (if flag then plus x else times x) y

  @[noinline] def pack (flag : Bool) (x : UInt64) : Option (UInt64 → UInt64) :=
    some (if flag then plus x else times x)

  def runPacked (flag : Bool) (x y : UInt64) : UInt64 :=
    match pack flag x with
    | none => 0
    | some f => f y
end FunctionProbe

run_cmd do
  let roots := #[``FunctionProbe.plus, ``FunctionProbe.times,
    ``FunctionProbe.choose, ``FunctionProbe.run, ``FunctionProbe.runDirect,
    ``FunctionProbe.applyValue, ``FunctionProbe.runIndirect,
    ``FunctionProbe.pack, ``FunctionProbe.runPacked]
  let snapshots ← liftCoreM do
    Lean.Compiler.compile roots
    let mut output : Array (Lean.Name × String) := #[]
    for root in roots do
      let some decl ← Lean.IR.findDecl root
        | throwError "missing IR {root}"
      output := output.push (root, toString decl)
    return output
  let generated ← liftCoreM do
    let names := #[
      ``FunctionProbe.runIndirect._lam_0._boxed,
      ``FunctionProbe.runIndirect._lam_0,
      ``FunctionProbe.pack._lam_0._boxed
    ]
    let mut found : Array (Lean.Name × String) := #[]
    for name in names do
      if let some decl ← Lean.IR.findDecl name then
        found := found.push (name, toString decl)
    return found
  for (name, ir) in generated do
    logInfo m!"GENERATED_CLOSURE_IR_START {name}"
    logInfo m!"{ir}"
    logInfo m!"GENERATED_CLOSURE_IR_END {name}"
  for (root, ir) in snapshots do
    logInfo m!"FUNCTION_IR_PROBE_START {root}"
    logInfo m!"{ir}"
    logInfo m!"FUNCTION_IR_PROBE_END {root}"
