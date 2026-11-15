import MutKernels

-- Pure driver: original declarations are compiled unchanged by Lean C.
def main (inputs : List String) : IO Unit := do
  let args := inputs.toArray
  if args.size % 2 != 0 then
    throw <| IO.userError "expected decimal Nat pairs"
  let n := args.size / 2
  for i in [:n] do
    let some a := args[2 * i]!.toNat?
      | throw <| IO.userError "invalid left Nat"
    let some b := args[2 * i + 1]!.toNat?
      | throw <| IO.userError "invalid right Nat"
    IO.println s!"{MutFixture.unique a b} {MutFixture.shared a b}"
