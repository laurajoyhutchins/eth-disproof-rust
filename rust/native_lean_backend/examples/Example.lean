import NativeRust

namespace Example

def addOne (x : UInt64) : UInt64 := x + 1
def timesThree (x : UInt64) : UInt64 := x * 3
def subtractSeven (x : UInt64) : UInt64 := x - 7
def twoArgs (x y : UInt64) : UInt64 := x + y

def multi (x : UInt64) : UInt64 := (x + 5) * 3

def choose (x : UInt64) : UInt64 := if x == 0 then 1 else x
def clamp (x y : UInt64) : UInt64 := if x < y then x else y
def minusIf (x : UInt64) : UInt64 := if x == 0 then 0 else x - 1
def eq (x y : UInt64) : Bool := x == y
def add32 (x : UInt32) : UInt32 := x * 3 + 2
def addSize (x : USize) : USize := x + 7
def tiny8 (x : UInt8) : UInt8 := x * 3 + 7
def tiny16 (x : UInt16) : UInt16 := x + 12
def less32 (x y : UInt32) : Bool := x < y
def leq64 (x y : UInt64) : Bool := x ≤ y

#guard addOne 41 == 42
#guard timesThree 7 == 21
#guard subtractSeven 3 == (3 - 7 : UInt64)
#guard twoArgs 2 3 == 5
#guard multi 7 == 36
#guard choose 0 == 1
#guard clamp 4 7 == 4
#guard minusIf 0 == 0
#guard eq 2 2 == true
#guard add32 5 == 17
#guard addSize 7 == 14
#guard tiny8 3 == 16
#guard tiny16 3 == 15
#guard less32 3 7 == true
#guard leq64 4 4 == true
#guard leq64 5 4 == false

end Example

#native_rust Example.addOne as "add_one" to "examples/generated_add_one.rs"
#native_rust Example.timesThree as "times_three" to "examples/generated_times_three.rs"
#native_rust Example.subtractSeven as "subtract_seven" to "examples/generated_subtract_seven.rs"
#native_rust Example.twoArgs as "two_args" to "examples/generated_two_args.rs"
#native_rust Example.multi as "multi" to "examples/generated_multi.rs"

#native_rust Example.choose as "choose" to "examples/generated_choose.rs"
#native_rust Example.clamp as "clamp" to "examples/generated_clamp.rs"
#native_rust Example.minusIf as "minus_if" to "examples/generated_minus_if.rs"
#native_rust Example.eq as "eq_uint" to "examples/generated_eq_uint.rs"
#native_rust Example.add32 as "add32" to "examples/generated_add32.rs"
#native_rust Example.addSize as "add_size" to "examples/generated_add_size.rs"
#native_rust Example.tiny8 as "tiny8" to "examples/generated_tiny8.rs"
#native_rust Example.tiny16 as "tiny16" to "examples/generated_tiny16.rs"
#native_rust Example.less32 as "less32" to "examples/generated_less32.rs"
#native_rust Example.leq64 as "leq64" to "examples/generated_leq64.rs"

open Lean Elab Command
-- Independently evaluate the original Lean definitions for reproducible
-- differential test vectors. The Rust emitter sees only IR; it does not
-- consume these results, and neither compiler uses JSON as an IR bridge.
run_cmd do
  let mut lines := "{\n"
  let mut x : UInt64 := 0x123456789ABCDEF0
  let mut y : UInt64 := 0x0FEDCBA987654321
  let edges : Array UInt64 := #[0, 1, 2, 3, 7, 42, UInt64.ofNat (2^32-1),
                                UInt64.ofNat (2^32), UInt64.ofNat (2^63), UInt64.ofNat (2^64-1)]
  for index in [:160] do
    if index < edges.size then
      x := edges[index]!
      y := edges[(edges.size - 1 - index)]!
    else
      x := x * 6364136223846793005 + 1442695040888963407
      y := y * 2862933555777941757 + 3037000493
    let n := x.toNat
    let m := y.toNat
    let choice := (Example.choose x).toNat
    let clamp := (Example.clamp x y).toNat
    let sub := (Example.minusIf x).toNat
    let equality := if Example.eq x y then 1 else 0
    let u32val := (Example.add32 (UInt32.ofNat n)).toNat
    let sizeval := (Example.addSize (USize.ofNat n)).toNat
    let eight := (Example.tiny8 (UInt8.ofNat n)).toNat
    let sixteen := (Example.tiny16 (UInt16.ofNat n)).toNat
    let l32 := if Example.less32 (UInt32.ofNat n) (UInt32.ofNat m) then 1 else 0
    let leq := if Example.leq64 x y then 1 else 0
    lines := lines ++ s!"    assert_eq!(choose({n}u64), {choice}u64);\n"
    lines := lines ++ s!"    assert_eq!(clamp({n}u64, {m}u64), {clamp}u64);\n"
    lines := lines ++ s!"    assert_eq!(minus_if({n}u64), {sub}u64);\n"
    lines := lines ++ s!"    assert_eq!(eq_uint({n}u64, {m}u64), {equality}u8);\n"
    lines := lines ++ s!"    assert_eq!(add32({(UInt32.ofNat n).toNat}u32), {u32val}u32);\n"
    lines := lines ++ s!"    assert_eq!(add_size({(USize.ofNat n).toNat}usize), {sizeval}usize);\n"
    lines := lines ++ s!"    assert_eq!(tiny8({(UInt8.ofNat n).toNat}u8), {eight}u8);\n"
    lines := lines ++ s!"    assert_eq!(tiny16({(UInt16.ofNat n).toNat}u16), {sixteen}u16);\n"
    lines := lines ++ s!"    assert_eq!(less32({(UInt32.ofNat n).toNat}u32, {(UInt32.ofNat m).toNat}u32), {l32}u8);\n"
    lines := lines ++ s!"    assert_eq!(leq64({n}u64, {m}u64), {leq}u8);\n"
  lines := lines ++ "}\n"
  liftIO <| IO.FS.writeFile "examples/generated_differential.rs" lines
  logInfo "Generated 1600 independently evaluated Lean/Rust assertions"
