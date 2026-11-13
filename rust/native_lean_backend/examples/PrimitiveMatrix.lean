import NativeRust

/- Each source function is compiled from genuine pinned Lean IR, never hand-written Rust. -/
namespace PrimitiveMatrix
def u8_add (x y : UInt8) : UInt8 := x + y
def u8_sub (x y : UInt8) : UInt8 := x - y
def u8_mul (x y : UInt8) : UInt8 := x * y
def u8_decEq (x y : UInt8) : Bool := x == y
def u8_decLt (x y : UInt8) : Bool := x < y
def u8_decLe (x y : UInt8) : Bool := x ≤ y

def u16_add (x y : UInt16) : UInt16 := x + y
def u16_sub (x y : UInt16) : UInt16 := x - y
def u16_mul (x y : UInt16) : UInt16 := x * y
def u16_decEq (x y : UInt16) : Bool := x == y
def u16_decLt (x y : UInt16) : Bool := x < y
def u16_decLe (x y : UInt16) : Bool := x ≤ y

def u32_add (x y : UInt32) : UInt32 := x + y
def u32_sub (x y : UInt32) : UInt32 := x - y
def u32_mul (x y : UInt32) : UInt32 := x * y
def u32_decEq (x y : UInt32) : Bool := x == y
def u32_decLt (x y : UInt32) : Bool := x < y
def u32_decLe (x y : UInt32) : Bool := x ≤ y

def u64_add (x y : UInt64) : UInt64 := x + y
def u64_sub (x y : UInt64) : UInt64 := x - y
def u64_mul (x y : UInt64) : UInt64 := x * y
def u64_decEq (x y : UInt64) : Bool := x == y
def u64_decLt (x y : UInt64) : Bool := x < y
def u64_decLe (x y : UInt64) : Bool := x ≤ y

def usize_add (x y : USize) : USize := x + y
def usize_sub (x y : USize) : USize := x - y
def usize_mul (x y : USize) : USize := x * y
def usize_decEq (x y : USize) : Bool := x == y
def usize_decLt (x y : USize) : Bool := x < y
def usize_decLe (x y : USize) : Bool := x ≤ y

end PrimitiveMatrix

#native_rust PrimitiveMatrix.u8_add as "matrix_u8_add" to "examples/generated_matrix_u8_add.rs"
#native_rust PrimitiveMatrix.u8_sub as "matrix_u8_sub" to "examples/generated_matrix_u8_sub.rs"
#native_rust PrimitiveMatrix.u8_mul as "matrix_u8_mul" to "examples/generated_matrix_u8_mul.rs"
#native_rust PrimitiveMatrix.u8_decEq as "matrix_u8_decEq" to "examples/generated_matrix_u8_decEq.rs"
#native_rust PrimitiveMatrix.u8_decLt as "matrix_u8_decLt" to "examples/generated_matrix_u8_decLt.rs"
#native_rust PrimitiveMatrix.u8_decLe as "matrix_u8_decLe" to "examples/generated_matrix_u8_decLe.rs"
#native_rust PrimitiveMatrix.u16_add as "matrix_u16_add" to "examples/generated_matrix_u16_add.rs"
#native_rust PrimitiveMatrix.u16_sub as "matrix_u16_sub" to "examples/generated_matrix_u16_sub.rs"
#native_rust PrimitiveMatrix.u16_mul as "matrix_u16_mul" to "examples/generated_matrix_u16_mul.rs"
#native_rust PrimitiveMatrix.u16_decEq as "matrix_u16_decEq" to "examples/generated_matrix_u16_decEq.rs"
#native_rust PrimitiveMatrix.u16_decLt as "matrix_u16_decLt" to "examples/generated_matrix_u16_decLt.rs"
#native_rust PrimitiveMatrix.u16_decLe as "matrix_u16_decLe" to "examples/generated_matrix_u16_decLe.rs"
#native_rust PrimitiveMatrix.u32_add as "matrix_u32_add" to "examples/generated_matrix_u32_add.rs"
#native_rust PrimitiveMatrix.u32_sub as "matrix_u32_sub" to "examples/generated_matrix_u32_sub.rs"
#native_rust PrimitiveMatrix.u32_mul as "matrix_u32_mul" to "examples/generated_matrix_u32_mul.rs"
#native_rust PrimitiveMatrix.u32_decEq as "matrix_u32_decEq" to "examples/generated_matrix_u32_decEq.rs"
#native_rust PrimitiveMatrix.u32_decLt as "matrix_u32_decLt" to "examples/generated_matrix_u32_decLt.rs"
#native_rust PrimitiveMatrix.u32_decLe as "matrix_u32_decLe" to "examples/generated_matrix_u32_decLe.rs"
#native_rust PrimitiveMatrix.u64_add as "matrix_u64_add" to "examples/generated_matrix_u64_add.rs"
#native_rust PrimitiveMatrix.u64_sub as "matrix_u64_sub" to "examples/generated_matrix_u64_sub.rs"
#native_rust PrimitiveMatrix.u64_mul as "matrix_u64_mul" to "examples/generated_matrix_u64_mul.rs"
#native_rust PrimitiveMatrix.u64_decEq as "matrix_u64_decEq" to "examples/generated_matrix_u64_decEq.rs"
#native_rust PrimitiveMatrix.u64_decLt as "matrix_u64_decLt" to "examples/generated_matrix_u64_decLt.rs"
#native_rust PrimitiveMatrix.u64_decLe as "matrix_u64_decLe" to "examples/generated_matrix_u64_decLe.rs"
#native_rust PrimitiveMatrix.usize_add as "matrix_usize_add" to "examples/generated_matrix_usize_add.rs"
#native_rust PrimitiveMatrix.usize_sub as "matrix_usize_sub" to "examples/generated_matrix_usize_sub.rs"
#native_rust PrimitiveMatrix.usize_mul as "matrix_usize_mul" to "examples/generated_matrix_usize_mul.rs"
#native_rust PrimitiveMatrix.usize_decEq as "matrix_usize_decEq" to "examples/generated_matrix_usize_decEq.rs"
#native_rust PrimitiveMatrix.usize_decLt as "matrix_usize_decLt" to "examples/generated_matrix_usize_decLt.rs"
#native_rust PrimitiveMatrix.usize_decLe as "matrix_usize_decLe" to "examples/generated_matrix_usize_decLe.rs"

open Lean Elab Command
run_cmd do
  let mut lines := "{\n"
  let edges : Array UInt64 := #[0, 1, 2, 3, 7, 42, UInt64.ofNat (2^32-1),
                                UInt64.ofNat (2^32), UInt64.ofNat (2^63), UInt64.ofNat (2^64-1)]
  let mut x : UInt64 := 0x123456789ABCDEF0
  let mut y : UInt64 := 0x0FEDCBA987654321
  for idx in [:64] do
    if idx < edges.size then
      x := edges[idx]!
      y := edges[edges.size - idx - 1]!
    else
      x := x * 6364136223846793005 + 1442695040888963407
      y := y * 2862933555777941757 + 3037000493
    if idx % 5 == 0 then y := x
    let a_u8 := UInt8.ofNat x.toNat
    let b_u8 := UInt8.ofNat y.toNat
    lines := lines ++ s!"    assert_eq!(matrix_u8_add({a_u8.toNat}u8, {b_u8.toNat}u8), {(PrimitiveMatrix.u8_add a_u8 b_u8).toNat}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u8_sub({a_u8.toNat}u8, {b_u8.toNat}u8), {(PrimitiveMatrix.u8_sub a_u8 b_u8).toNat}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u8_mul({a_u8.toNat}u8, {b_u8.toNat}u8), {(PrimitiveMatrix.u8_mul a_u8 b_u8).toNat}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u8_decEq({a_u8.toNat}u8, {b_u8.toNat}u8), {(if PrimitiveMatrix.u8_decEq a_u8 b_u8 then 1 else 0)}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u8_decLt({a_u8.toNat}u8, {b_u8.toNat}u8), {(if PrimitiveMatrix.u8_decLt a_u8 b_u8 then 1 else 0)}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u8_decLe({a_u8.toNat}u8, {b_u8.toNat}u8), {(if PrimitiveMatrix.u8_decLe a_u8 b_u8 then 1 else 0)}u8);\n"
    let a_u16 := UInt16.ofNat x.toNat
    let b_u16 := UInt16.ofNat y.toNat
    lines := lines ++ s!"    assert_eq!(matrix_u16_add({a_u16.toNat}u16, {b_u16.toNat}u16), {(PrimitiveMatrix.u16_add a_u16 b_u16).toNat}u16);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u16_sub({a_u16.toNat}u16, {b_u16.toNat}u16), {(PrimitiveMatrix.u16_sub a_u16 b_u16).toNat}u16);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u16_mul({a_u16.toNat}u16, {b_u16.toNat}u16), {(PrimitiveMatrix.u16_mul a_u16 b_u16).toNat}u16);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u16_decEq({a_u16.toNat}u16, {b_u16.toNat}u16), {(if PrimitiveMatrix.u16_decEq a_u16 b_u16 then 1 else 0)}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u16_decLt({a_u16.toNat}u16, {b_u16.toNat}u16), {(if PrimitiveMatrix.u16_decLt a_u16 b_u16 then 1 else 0)}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u16_decLe({a_u16.toNat}u16, {b_u16.toNat}u16), {(if PrimitiveMatrix.u16_decLe a_u16 b_u16 then 1 else 0)}u8);\n"
    let a_u32 := UInt32.ofNat x.toNat
    let b_u32 := UInt32.ofNat y.toNat
    lines := lines ++ s!"    assert_eq!(matrix_u32_add({a_u32.toNat}u32, {b_u32.toNat}u32), {(PrimitiveMatrix.u32_add a_u32 b_u32).toNat}u32);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u32_sub({a_u32.toNat}u32, {b_u32.toNat}u32), {(PrimitiveMatrix.u32_sub a_u32 b_u32).toNat}u32);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u32_mul({a_u32.toNat}u32, {b_u32.toNat}u32), {(PrimitiveMatrix.u32_mul a_u32 b_u32).toNat}u32);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u32_decEq({a_u32.toNat}u32, {b_u32.toNat}u32), {(if PrimitiveMatrix.u32_decEq a_u32 b_u32 then 1 else 0)}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u32_decLt({a_u32.toNat}u32, {b_u32.toNat}u32), {(if PrimitiveMatrix.u32_decLt a_u32 b_u32 then 1 else 0)}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u32_decLe({a_u32.toNat}u32, {b_u32.toNat}u32), {(if PrimitiveMatrix.u32_decLe a_u32 b_u32 then 1 else 0)}u8);\n"
    let a_u64 := UInt64.ofNat x.toNat
    let b_u64 := UInt64.ofNat y.toNat
    lines := lines ++ s!"    assert_eq!(matrix_u64_add({a_u64.toNat}u64, {b_u64.toNat}u64), {(PrimitiveMatrix.u64_add a_u64 b_u64).toNat}u64);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u64_sub({a_u64.toNat}u64, {b_u64.toNat}u64), {(PrimitiveMatrix.u64_sub a_u64 b_u64).toNat}u64);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u64_mul({a_u64.toNat}u64, {b_u64.toNat}u64), {(PrimitiveMatrix.u64_mul a_u64 b_u64).toNat}u64);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u64_decEq({a_u64.toNat}u64, {b_u64.toNat}u64), {(if PrimitiveMatrix.u64_decEq a_u64 b_u64 then 1 else 0)}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u64_decLt({a_u64.toNat}u64, {b_u64.toNat}u64), {(if PrimitiveMatrix.u64_decLt a_u64 b_u64 then 1 else 0)}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_u64_decLe({a_u64.toNat}u64, {b_u64.toNat}u64), {(if PrimitiveMatrix.u64_decLe a_u64 b_u64 then 1 else 0)}u8);\n"
    let a_usize := USize.ofNat x.toNat
    let b_usize := USize.ofNat y.toNat
    lines := lines ++ s!"    assert_eq!(matrix_usize_add({a_usize.toNat}usize, {b_usize.toNat}usize), {(PrimitiveMatrix.usize_add a_usize b_usize).toNat}usize);\n"
    lines := lines ++ s!"    assert_eq!(matrix_usize_sub({a_usize.toNat}usize, {b_usize.toNat}usize), {(PrimitiveMatrix.usize_sub a_usize b_usize).toNat}usize);\n"
    lines := lines ++ s!"    assert_eq!(matrix_usize_mul({a_usize.toNat}usize, {b_usize.toNat}usize), {(PrimitiveMatrix.usize_mul a_usize b_usize).toNat}usize);\n"
    lines := lines ++ s!"    assert_eq!(matrix_usize_decEq({a_usize.toNat}usize, {b_usize.toNat}usize), {(if PrimitiveMatrix.usize_decEq a_usize b_usize then 1 else 0)}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_usize_decLt({a_usize.toNat}usize, {b_usize.toNat}usize), {(if PrimitiveMatrix.usize_decLt a_usize b_usize then 1 else 0)}u8);\n"
    lines := lines ++ s!"    assert_eq!(matrix_usize_decLe({a_usize.toNat}usize, {b_usize.toNat}usize), {(if PrimitiveMatrix.usize_decLe a_usize b_usize then 1 else 0)}u8);\n"
  lines := lines ++ "}\n"
  liftIO <| IO.FS.writeFile "examples/generated_matrix_assertions.rs" lines
  logInfo "Generated 1,920 independently Lean-evaluated primitive-matrix assertions"
