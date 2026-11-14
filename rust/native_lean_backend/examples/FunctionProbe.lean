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
end FunctionProbe

run_cmd do
  let roots := #[``FunctionProbe.plus, ``FunctionProbe.times,
    ``FunctionProbe.choose, ``FunctionProbe.run, ``FunctionProbe.runDirect]
  Lean.Compiler.compile roots
  for root in roots do
    let some decl ← Lean.IR.findDecl root
      | throwError "missing IR {root}"
    logInfo m!"FUNCTION_IR_PROBE_START {root}"
    logInfo m!"{toString decl}"
    logInfo m!"FUNCTION_IR_PROBE_END {root}"
