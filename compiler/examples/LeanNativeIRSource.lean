namespace LeanNativeIRFixture

@[noinline] def add (x y : UInt64) : UInt64 := x + y

@[noinline] def pipeline (x y : UInt64) : UInt64 :=
  add (x + 7) (add x y)

@[noinline] def choose (x y : UInt64) : UInt64 :=
  if x == 0 then y else x

end LeanNativeIRFixture
