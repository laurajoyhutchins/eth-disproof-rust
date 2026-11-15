import BenchmarkKernels

namespace BenchmarkDriver

def arrayChecksum (iterations : Nat) : UInt64 := Id.run do
  let mut state : UInt64 := 0x31415926D00DCAFE
  let mut total : UInt64 := 0
  for i in [:iterations] do
    state := state * 6364136223846793005 + 1442695040888963407
    total := total + BenchmarkKernels.arrayStep state (state + UInt64.ofNat i)
  return total

def closureChecksum (iterations : Nat) : UInt64 := Id.run do
  let mut state : UInt64 := 0x9E3779B97F4A7C15
  let mut total : UInt64 := 0
  for i in [:iterations] do
    state := state * 2862933555777941757 + 3037000493
    let flag := i % 2 == 0
    total := total + BenchmarkKernels.closureStep flag state (state + 7) (state + 19)
  return total

def natChecksum (iterations : Nat) : Nat := Id.run do
  let a0 : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639953
  let a1 : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129640015
  let b0 : Nat := 340282366920938463463374607431768211489
  let b1 : Nat := 340282366920938463463374607431768211517
  let mut total : Nat := 0
  for i in [:iterations] do
    let a := if i % 2 == 0 then a0 else a1
    let b := if i % 3 == 0 then b0 else b1
    total := BenchmarkKernels.natAccumulate total (BenchmarkKernels.natStep a b)
  return total

end BenchmarkDriver

def main (args : List String) : IO Unit := do
  match args with
  | [kind, count] =>
    let some n := count.toNat?
      | throw <| IO.userError "count must be a Nat"
    if kind == "array" then
      IO.println (BenchmarkDriver.arrayChecksum n).toNat
    else if kind == "closure" then
      IO.println (BenchmarkDriver.closureChecksum n).toNat
    else if kind == "nat" then
      IO.println (BenchmarkDriver.natChecksum n)
    else
      throw <| IO.userError "expected array, closure, or nat"
  | _ => throw <| IO.userError "usage: BenchmarkDriver array|closure|nat COUNT"
