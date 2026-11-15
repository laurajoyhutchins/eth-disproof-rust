-- Source of truth for both Lean's native C backend and the in-process Rust emitter.
-- No native Rust implementation of these routines is provided.
namespace BenchmarkKernels

@[noinline] def arrayStep (x y : UInt64) : UInt64 :=
  let a : Array UInt64 := #[x, y]
  let b := a.set! 0 (x + 1)
  let c := b.push (x + y)
  a.getD 0 0 + c.getD 0 0 + c.getD 2 0

@[noinline] def plus (a b : UInt64) : UInt64 := a + b
@[noinline] def times (a b : UInt64) : UInt64 := a * b
@[noinline] def applyValue (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f x

@[noinline] def closureStep (flag : Bool) (x y z : UInt64) : UInt64 :=
  let f := if flag then plus x else times x
  applyValue f y + applyValue f z

@[noinline] def natStep (a b : Nat) : Nat :=
  let divisor := b + 1
  ((a * b + a) % divisor) + a / divisor

@[noinline] def natAccumulate (a b : Nat) : Nat := a + b

end BenchmarkKernels
