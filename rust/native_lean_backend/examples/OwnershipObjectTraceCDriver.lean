-- The executable driver uses the *same explicit reference-transfer
-- schedule as the Rust test*. Only the pure source kernel is compiled by
-- both backends. The C companion owns the calls and the object observations.
@[extern "lr_object_trace_run"] opaque traceRun (a b : Nat) : Nat

def main (args : List String) : IO Unit := do
  let words := args.toArray
  if words.size != 2 then
    throw <| IO.userError "expected two runtime Nat inputs"
  let some first := words[0]!.toNat?
    | throw <| IO.userError "first argument is not a Nat"
  let some second := words[1]!.toNat?
    | throw <| IO.userError "second argument is not a Nat"
  IO.println (traceRun first second)
