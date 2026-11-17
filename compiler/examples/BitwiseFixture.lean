import NativeRust

namespace BitwiseFixture
  def and8 (a b : UInt8) : UInt8 := a &&& b
  def or8 (a b : UInt8) : UInt8 := a ||| b
  def xor8 (a b : UInt8) : UInt8 := a ^^^ b
  def left8 (a b : UInt8) : UInt8 := a <<< b
  def right8 (a b : UInt8) : UInt8 := a >>> b
  def div8 (a b : UInt8) : UInt8 := a / b
  def mod8 (a b : UInt8) : UInt8 := a % b
  def and16 (a b : UInt16) : UInt16 := a &&& b
  def or16 (a b : UInt16) : UInt16 := a ||| b
  def xor16 (a b : UInt16) : UInt16 := a ^^^ b
  def left16 (a b : UInt16) : UInt16 := a <<< b
  def right16 (a b : UInt16) : UInt16 := a >>> b
  def div16 (a b : UInt16) : UInt16 := a / b
  def mod16 (a b : UInt16) : UInt16 := a % b
  def and32 (a b : UInt32) : UInt32 := a &&& b
  def or32 (a b : UInt32) : UInt32 := a ||| b
  def xor32 (a b : UInt32) : UInt32 := a ^^^ b
  def left32 (a b : UInt32) : UInt32 := a <<< b
  def right32 (a b : UInt32) : UInt32 := a >>> b
  def div32 (a b : UInt32) : UInt32 := a / b
  def mod32 (a b : UInt32) : UInt32 := a % b
  def and64 (a b : UInt64) : UInt64 := a &&& b
  def or64 (a b : UInt64) : UInt64 := a ||| b
  def xor64 (a b : UInt64) : UInt64 := a ^^^ b
  def left64 (a b : UInt64) : UInt64 := a <<< b
  def right64 (a b : UInt64) : UInt64 := a >>> b
  def div64 (a b : UInt64) : UInt64 := a / b
  def mod64 (a b : UInt64) : UInt64 := a % b
  def andSize (a b : USize) : USize := a &&& b
  def orSize (a b : USize) : USize := a ||| b
  def xorSize (a b : USize) : USize := a ^^^ b
  def leftSize (a b : USize) : USize := a <<< b
  def rightSize (a b : USize) : USize := a >>> b
  def divSize (a b : USize) : USize := a / b
  def modSize (a b : USize) : USize := a % b
end BitwiseFixture

#native_rust_closure BitwiseFixture.and8 as "bw_and8" to "examples/generated_bw_and8.rs"
#native_rust_closure BitwiseFixture.or8 as "bw_or8" to "examples/generated_bw_or8.rs"
#native_rust_closure BitwiseFixture.xor8 as "bw_xor8" to "examples/generated_bw_xor8.rs"
#native_rust_closure BitwiseFixture.left8 as "bw_left8" to "examples/generated_bw_left8.rs"
#native_rust_closure BitwiseFixture.right8 as "bw_right8" to "examples/generated_bw_right8.rs"
#native_rust_closure BitwiseFixture.div8 as "bw_div8" to "examples/generated_bw_div8.rs"
#native_rust_closure BitwiseFixture.mod8 as "bw_mod8" to "examples/generated_bw_mod8.rs"
#native_rust_closure BitwiseFixture.and16 as "bw_and16" to "examples/generated_bw_and16.rs"
#native_rust_closure BitwiseFixture.or16 as "bw_or16" to "examples/generated_bw_or16.rs"
#native_rust_closure BitwiseFixture.xor16 as "bw_xor16" to "examples/generated_bw_xor16.rs"
#native_rust_closure BitwiseFixture.left16 as "bw_left16" to "examples/generated_bw_left16.rs"
#native_rust_closure BitwiseFixture.right16 as "bw_right16" to "examples/generated_bw_right16.rs"
#native_rust_closure BitwiseFixture.div16 as "bw_div16" to "examples/generated_bw_div16.rs"
#native_rust_closure BitwiseFixture.mod16 as "bw_mod16" to "examples/generated_bw_mod16.rs"
#native_rust_closure BitwiseFixture.and32 as "bw_and32" to "examples/generated_bw_and32.rs"
#native_rust_closure BitwiseFixture.or32 as "bw_or32" to "examples/generated_bw_or32.rs"
#native_rust_closure BitwiseFixture.xor32 as "bw_xor32" to "examples/generated_bw_xor32.rs"
#native_rust_closure BitwiseFixture.left32 as "bw_left32" to "examples/generated_bw_left32.rs"
#native_rust_closure BitwiseFixture.right32 as "bw_right32" to "examples/generated_bw_right32.rs"
#native_rust_closure BitwiseFixture.div32 as "bw_div32" to "examples/generated_bw_div32.rs"
#native_rust_closure BitwiseFixture.mod32 as "bw_mod32" to "examples/generated_bw_mod32.rs"
#native_rust_closure BitwiseFixture.and64 as "bw_and64" to "examples/generated_bw_and64.rs"
#native_rust_closure BitwiseFixture.or64 as "bw_or64" to "examples/generated_bw_or64.rs"
#native_rust_closure BitwiseFixture.xor64 as "bw_xor64" to "examples/generated_bw_xor64.rs"
#native_rust_closure BitwiseFixture.left64 as "bw_left64" to "examples/generated_bw_left64.rs"
#native_rust_closure BitwiseFixture.right64 as "bw_right64" to "examples/generated_bw_right64.rs"
#native_rust_closure BitwiseFixture.div64 as "bw_div64" to "examples/generated_bw_div64.rs"
#native_rust_closure BitwiseFixture.mod64 as "bw_mod64" to "examples/generated_bw_mod64.rs"
#native_rust_closure BitwiseFixture.andSize as "bw_andSize" to "examples/generated_bw_andSize.rs"
#native_rust_closure BitwiseFixture.orSize as "bw_orSize" to "examples/generated_bw_orSize.rs"
#native_rust_closure BitwiseFixture.xorSize as "bw_xorSize" to "examples/generated_bw_xorSize.rs"
#native_rust_closure BitwiseFixture.leftSize as "bw_leftSize" to "examples/generated_bw_leftSize.rs"
#native_rust_closure BitwiseFixture.rightSize as "bw_rightSize" to "examples/generated_bw_rightSize.rs"
#native_rust_closure BitwiseFixture.divSize as "bw_divSize" to "examples/generated_bw_divSize.rs"
#native_rust_closure BitwiseFixture.modSize as "bw_modSize" to "examples/generated_bw_modSize.rs"

open Lean Elab Command
run_cmd do
  let mut test := "{\n"
  for i in [:64] do
    let a8 : UInt8 := UInt8.ofNat (if i % 13 == 0 then 255 else i * 999999971 + 421)
    let b8 : UInt8 := UInt8.ofNat (if i % 11 == 0 then 0 else if i == 1 then 1 else if i == 2 then 8 else if i == 3 then 16 else if i == 4 then 32 else if i == 5 then 64 else if i == 6 then 65 else i * 114007 + 64)
    test := test ++ s!"assert_eq!(bw_and8({a8.toNat}u8,{b8.toNat}u8),{(BitwiseFixture.and8 a8 b8).toNat}u8);\n"
    test := test ++ s!"assert_eq!(bw_or8({a8.toNat}u8,{b8.toNat}u8),{(BitwiseFixture.or8 a8 b8).toNat}u8);\n"
    test := test ++ s!"assert_eq!(bw_xor8({a8.toNat}u8,{b8.toNat}u8),{(BitwiseFixture.xor8 a8 b8).toNat}u8);\n"
    test := test ++ s!"assert_eq!(bw_left8({a8.toNat}u8,{b8.toNat}u8),{(BitwiseFixture.left8 a8 b8).toNat}u8);\n"
    test := test ++ s!"assert_eq!(bw_right8({a8.toNat}u8,{b8.toNat}u8),{(BitwiseFixture.right8 a8 b8).toNat}u8);\n"
    test := test ++ s!"assert_eq!(bw_div8({a8.toNat}u8,{b8.toNat}u8),{(BitwiseFixture.div8 a8 b8).toNat}u8);\n"
    test := test ++ s!"assert_eq!(bw_mod8({a8.toNat}u8,{b8.toNat}u8),{(BitwiseFixture.mod8 a8 b8).toNat}u8);\n"
    let a16 : UInt16 := UInt16.ofNat (if i % 13 == 0 then 65535 else i * 999999971 + 421)
    let b16 : UInt16 := UInt16.ofNat (if i % 11 == 0 then 0 else if i == 1 then 1 else if i == 2 then 8 else if i == 3 then 16 else if i == 4 then 32 else if i == 5 then 64 else if i == 6 then 65 else i * 114007 + 64)
    test := test ++ s!"assert_eq!(bw_and16({a16.toNat}u16,{b16.toNat}u16),{(BitwiseFixture.and16 a16 b16).toNat}u16);\n"
    test := test ++ s!"assert_eq!(bw_or16({a16.toNat}u16,{b16.toNat}u16),{(BitwiseFixture.or16 a16 b16).toNat}u16);\n"
    test := test ++ s!"assert_eq!(bw_xor16({a16.toNat}u16,{b16.toNat}u16),{(BitwiseFixture.xor16 a16 b16).toNat}u16);\n"
    test := test ++ s!"assert_eq!(bw_left16({a16.toNat}u16,{b16.toNat}u16),{(BitwiseFixture.left16 a16 b16).toNat}u16);\n"
    test := test ++ s!"assert_eq!(bw_right16({a16.toNat}u16,{b16.toNat}u16),{(BitwiseFixture.right16 a16 b16).toNat}u16);\n"
    test := test ++ s!"assert_eq!(bw_div16({a16.toNat}u16,{b16.toNat}u16),{(BitwiseFixture.div16 a16 b16).toNat}u16);\n"
    test := test ++ s!"assert_eq!(bw_mod16({a16.toNat}u16,{b16.toNat}u16),{(BitwiseFixture.mod16 a16 b16).toNat}u16);\n"
    let a32 : UInt32 := UInt32.ofNat (if i % 13 == 0 then 4294967295 else i * 999999971 + 421)
    let b32 : UInt32 := UInt32.ofNat (if i % 11 == 0 then 0 else if i == 1 then 1 else if i == 2 then 8 else if i == 3 then 16 else if i == 4 then 32 else if i == 5 then 64 else if i == 6 then 65 else i * 114007 + 64)
    test := test ++ s!"assert_eq!(bw_and32({a32.toNat}u32,{b32.toNat}u32),{(BitwiseFixture.and32 a32 b32).toNat}u32);\n"
    test := test ++ s!"assert_eq!(bw_or32({a32.toNat}u32,{b32.toNat}u32),{(BitwiseFixture.or32 a32 b32).toNat}u32);\n"
    test := test ++ s!"assert_eq!(bw_xor32({a32.toNat}u32,{b32.toNat}u32),{(BitwiseFixture.xor32 a32 b32).toNat}u32);\n"
    test := test ++ s!"assert_eq!(bw_left32({a32.toNat}u32,{b32.toNat}u32),{(BitwiseFixture.left32 a32 b32).toNat}u32);\n"
    test := test ++ s!"assert_eq!(bw_right32({a32.toNat}u32,{b32.toNat}u32),{(BitwiseFixture.right32 a32 b32).toNat}u32);\n"
    test := test ++ s!"assert_eq!(bw_div32({a32.toNat}u32,{b32.toNat}u32),{(BitwiseFixture.div32 a32 b32).toNat}u32);\n"
    test := test ++ s!"assert_eq!(bw_mod32({a32.toNat}u32,{b32.toNat}u32),{(BitwiseFixture.mod32 a32 b32).toNat}u32);\n"
    let a64 : UInt64 := UInt64.ofNat (if i % 13 == 0 then 18446744073709551615 else i * 999999971 + 421)
    let b64 : UInt64 := UInt64.ofNat (if i % 11 == 0 then 0 else if i == 1 then 1 else if i == 2 then 8 else if i == 3 then 16 else if i == 4 then 32 else if i == 5 then 64 else if i == 6 then 65 else i * 114007 + 64)
    test := test ++ s!"assert_eq!(bw_and64({a64.toNat}u64,{b64.toNat}u64),{(BitwiseFixture.and64 a64 b64).toNat}u64);\n"
    test := test ++ s!"assert_eq!(bw_or64({a64.toNat}u64,{b64.toNat}u64),{(BitwiseFixture.or64 a64 b64).toNat}u64);\n"
    test := test ++ s!"assert_eq!(bw_xor64({a64.toNat}u64,{b64.toNat}u64),{(BitwiseFixture.xor64 a64 b64).toNat}u64);\n"
    test := test ++ s!"assert_eq!(bw_left64({a64.toNat}u64,{b64.toNat}u64),{(BitwiseFixture.left64 a64 b64).toNat}u64);\n"
    test := test ++ s!"assert_eq!(bw_right64({a64.toNat}u64,{b64.toNat}u64),{(BitwiseFixture.right64 a64 b64).toNat}u64);\n"
    test := test ++ s!"assert_eq!(bw_div64({a64.toNat}u64,{b64.toNat}u64),{(BitwiseFixture.div64 a64 b64).toNat}u64);\n"
    test := test ++ s!"assert_eq!(bw_mod64({a64.toNat}u64,{b64.toNat}u64),{(BitwiseFixture.mod64 a64 b64).toNat}u64);\n"
    let aSize : USize := USize.ofNat (if i % 13 == 0 then 18446744073709551615 else i * 999999971 + 421)
    let bSize : USize := USize.ofNat (if i % 11 == 0 then 0 else if i == 1 then 1 else if i == 2 then 8 else if i == 3 then 16 else if i == 4 then 32 else if i == 5 then 64 else if i == 6 then 65 else i * 114007 + 64)
    test := test ++ s!"assert_eq!(bw_andSize({aSize.toNat}usize,{bSize.toNat}usize),{(BitwiseFixture.andSize aSize bSize).toNat}usize);\n"
    test := test ++ s!"assert_eq!(bw_orSize({aSize.toNat}usize,{bSize.toNat}usize),{(BitwiseFixture.orSize aSize bSize).toNat}usize);\n"
    test := test ++ s!"assert_eq!(bw_xorSize({aSize.toNat}usize,{bSize.toNat}usize),{(BitwiseFixture.xorSize aSize bSize).toNat}usize);\n"
    test := test ++ s!"assert_eq!(bw_leftSize({aSize.toNat}usize,{bSize.toNat}usize),{(BitwiseFixture.leftSize aSize bSize).toNat}usize);\n"
    test := test ++ s!"assert_eq!(bw_rightSize({aSize.toNat}usize,{bSize.toNat}usize),{(BitwiseFixture.rightSize aSize bSize).toNat}usize);\n"
    test := test ++ s!"assert_eq!(bw_divSize({aSize.toNat}usize,{bSize.toNat}usize),{(BitwiseFixture.divSize aSize bSize).toNat}usize);\n"
    test := test ++ s!"assert_eq!(bw_modSize({aSize.toNat}usize,{bSize.toNat}usize),{(BitwiseFixture.modSize aSize bSize).toNat}usize);\n"
  test := test ++ "}\n"
  liftIO <| IO.FS.writeFile "examples/generated_bitwise_differential.rs" test
  logInfo "Generated 2240 independently Lean-evaluated unsigned bitwise, shift, division, and remainder assertions"
