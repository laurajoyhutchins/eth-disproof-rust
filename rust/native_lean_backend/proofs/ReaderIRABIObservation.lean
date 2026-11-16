import ReaderIRBoolSoundness

/-!
# Pinned Lean IR borrowed-ABI readback

The C/Rust native observer traverses the *same borrowed in-process objects*
passed to production Reader. This file independently constructs a textual
structural observation from the genuine Lean.IR.Decl, then checks exact equality
with the native observation. It does not substitute a serialized input for the
production compiler.

The finite live-FFI checks below are a *tested ABI boundary*, not a Lean proof
that arbitrary memory/FFI pointers agree with Lean values. The separate
mathematical theorem establishes the exact 0/1 UInt8 encoding used by the
restricted source Bool-branch operational model.
-/

open Lean
open NativeRustScalarRefinement

namespace ReaderIRABIObservation

/-- A value-level UInt8 representation of a Bool comparison result. -/
def boolByte : Bool → UInt8
  | false => 0
  | true => 1

/-- Reject invalid UInt8 tags rather than interpreting every nonzero tag as
true. This corresponds to Reader's exhausted 0/1 alternatives and default
unreachable! branch, at the abstract target level. -/
def decodeBool (n : UInt8) : Option Bool :=
  if n == 0 then some false else if n == 1 then some true else none

theorem bool_byte_roundtrip (b : Bool) :
    decodeBool (boolByte b) = some b := by
  cases b <;> decide

theorem bool_byte_nat (b : Bool) :
    (boolByte b).toNat = rustBoolTag b := by
  cases b <;> decide

theorem bool_byte_branch (b : Bool) (t f : UInt64) :
    (if (boolByte b).toNat == 1 then t else f) =
      if b then t else f := by
  cases b <;> rfl

theorem compared_bool_byte_roundtrip (inputs : Nat → UInt64)
    (cond : Condition) :
    decodeBool (boolByte (evalActualCondition inputs cond)) =
      some (evalActualCondition inputs cond) :=
  bool_byte_roundtrip _

private def scalarTy : IR.IRType → Option String
  | .uint64 => some "u64"
  | .uint8 => some "u8"
  | _ => none

private def argId : IR.Arg → Option Nat
  | .var id => some id.idx
  | .erased => none

private def observeExpr : IR.Expr → Option String
  | .lit (.num n) => some s!"E L {n}\n"
  | .fap name args => do
      if args.size != 2 then none else
      let a ← args[0]? >>= argId
      let b ← args[1]? >>= argId
      let name := name.toString
      if !(#["UInt64.add", "UInt64.mul", "UInt64.decEq",
             "UInt64.decLt", "UInt64.decLe"].contains name) then none
      else some s!"E F {name} {a} {b}\n"
  | _ => none

/-- Independently render the *original* IR body constructors and metadata,
including both complete Bool alternatives, in original array order. This
function is not the emitter or the FFI observer. -/
private partial def observeBody : IR.FnBody → Option String
  | .vdecl id ty expr tail => do
      let ty ← scalarTy ty
      let rhs ← observeExpr expr
      let next ← observeBody tail
      return s!"V {id.idx} {ty}\n" ++ rhs ++ next
  | .ret arg => do
      let id ← argId arg
      return s!"RETURN {id}\n"
  | .case tid scr ty alts => do
      if tid.toString != "UInt8" || alts.size != 2 then none else
      let ty ← scalarTy ty
      if ty != "u8" then none else
      let mut result := s!"CASE {tid} {scr.idx} {ty} {alts.size}\n"
      let mut seenFalse := false
      let mut seenTrue := false
      for alt in alts do
        match alt with
        | .ctor info body =>
          let name := info.name.toString
          let cidx := info.cidx
          if cidx == 0 && name == "Bool.false" && !seenFalse then
            seenFalse := true
          else if cidx == 1 && name == "Bool.true" && !seenTrue then
            seenTrue := true
          else
            none
          let arm ← observeBody body
          result := result ++ s!"ALT {name} {cidx}\n" ++ arm ++ "ENDALT\n"
        | .default _ => none
      if !seenFalse || !seenTrue then none
      else some (result ++ "ENDCASE\n")
  | _ => none

/-- Complete strict two-parameter scalar function signature and body layout,
constructed in Lean from actual compiled Lean.IR.Decl. -/
def observeDecl : IR.Decl → Option String
  | .fdecl name params .uint64 body _ => do
      if params.size != 2 then none else
      let mut out := s!"DECL {name}\n"
      let mut seen : Array Nat := #[]
      for param in params do
        if param.borrow then none else
        let ty ← scalarTy param.ty
        if ty != "u64" || seen.contains param.x.idx then none else
        seen := seen.push param.x.idx
        out := out ++ s!"PARAM {param.x.idx} {ty} 0\n"
      let rest ← observeBody body
      return out ++ "RET u64\n" ++ rest
  | _ => none

end ReaderIRABIObservation

#print axioms ReaderIRABIObservation.bool_byte_roundtrip
#print axioms ReaderIRABIObservation.bool_byte_nat
#print axioms ReaderIRABIObservation.bool_byte_branch

open Lean Elab Command

run_cmd do
  for root in #[`ScalarFixture.plus, `ScalarFixture.straightChain,
                `ScalarFixture.choose, `ScalarFixture.nested] do
    let some decl ← liftCoreM <| IR.findDecl root
      | throwError "original compiler IR unavailable: {root}"
    unless (ReaderIRBoolSoundness.certifyDecl decl).isSome do
      throwError "ABI test fixture lacks source-IR semantic certificate: {root}"
    let some expected := ReaderIRABIObservation.observeDecl decl
      | throwError "independent Lean IR observer refused {root}"
    let observed ← liftCoreM <| NativeRust.observeScalarABI root
    unless observed == expected do
      throwError "C/Rust borrowed-IR observation differs from original Lean IR for {root}\nExpected:\n{expected}\nObserved:\n{observed}"
    logInfo m!"Actual borrowed C/Rust IR observation matched source Lean IR: {root}"
  let root := `ScalarFixture.subtract
  let some decl ← liftCoreM <| IR.findDecl root
    | throwError "negative source IR missing"
  unless (ReaderIRABIObservation.observeDecl decl).isNone do
    throwError "independent Lean scalar observer accidentally admitted subtraction"
  let observed := NativeRust.scalarABIObserve decl
  unless observed.startsWith "ERROR\n" do
    throwError "native borrowed-IR observer incorrectly admitted subtraction"
  logInfo "Native borrowed IR observation correctly rejected unsupported subtraction"
