import NativeRust
import ScalarOperationalRefinement
import ScalarFixture

/-!
An independent, fail-closed checker for the *actual* Reader output in the
proved UInt64 / Bool-branch fragment.

The Rust FFI emits the source. This file reads the original in-process
Lean.IR.Decl, constructs a ScalarOperationalRefinement.Program, and constructs
the exact expected Rust function text *independently* of Reader. The certificate
exists only when Reader's complete output equals the independently constructed
source byte for byte.

This is an emitter-to-modeled-syntax correspondence for a restricted fragment,
not an operational semantics of rustc, an ownership proof, or a proof about
all accepted Lean IR. Unsupported effects are not silently certified.
-/

open Lean
open NativeRustScalarRefinement

namespace ReaderScalarCertificate

private def require (test : Bool) : Option Unit :=
  if test then some () else none

private structure Bindings where
  words : Nat → Option WordExpr := fun _ => none
  tests : Nat → Option Condition := fun _ => none
  used : Nat → Bool := fun _ => false

private def Bindings.addWord (env : Bindings) (id : Nat) (value : WordExpr) : Bindings :=
  { env with
    words := fun n => if n == id then some value else env.words n
    used := fun n => if n == id then true else env.used n }

private def Bindings.addTest (env : Bindings) (id : Nat) (value : Condition) : Bindings :=
  { env with
    tests := fun n => if n == id then some value else env.tests n
    used := fun n => if n == id then true else env.used n }

private def argId (arg : IR.Arg) : Option Nat :=
  match arg with
  | .var x => some x.idx
  | .erased => none

private def pair (args : Array IR.Arg) : Option (Nat × Nat) := do
  let _ ← require (args.size == 2)
  let left ← args[0]?
  let right ← args[1]?
  return (← argId left, ← argId right)

private inductive Value where
  | word : WordExpr → Value
  | test : Condition → Value

/-- Reify a Reader-admitted scalar vdecl and independently render its RHS.
The source name, type and operand arity must match exactly. -/
private def reifyExpr (env : Bindings) (ty : IR.IRType)
    (expr : IR.Expr) : Option (Value × String) := do
  match expr with
  | .lit (.num n) =>
    let _ ← require (ty == .uint64 && n < modulus)
    return (.word (.lit n), s!"{n}u64")
  | .fap name args =>
    let (a, b) ← pair args
    let lhs ← env.words a
    let rhs ← env.words b
    let name := name.toString
    match name with
    | "UInt64.add" =>
      let _ ← require (ty == .uint64)
      return (.word (.add lhs rhs), s!"x_{a}.wrapping_add(x_{b})")
    | "UInt64.mul" =>
      let _ ← require (ty == .uint64)
      return (.word (.mul lhs rhs), s!"x_{a}.wrapping_mul(x_{b})")
    | "UInt64.decEq" =>
      let _ ← require (ty == .uint8)
      return (.test (.eq lhs rhs), s!"u8::from(x_{a} == x_{b})")
    | "UInt64.decLt" =>
      let _ ← require (ty == .uint8)
      return (.test (.lt lhs rhs), s!"u8::from(x_{a} < x_{b})")
    | "UInt64.decLe" =>
      let _ ← require (ty == .uint8)
      return (.test (.le lhs rhs), s!"u8::from(x_{a} <= x_{b})")
    | _ => none
  | _ => none

/-- Independently reconstruct the exact source for the same bounded subset
of Reader's FnBody grammar. Branch environments are immutable, so definitions
in one arm cannot leak into another. -/
private partial def reifyBody (env : Bindings)
    (body : IR.FnBody) : Option (Program × String) := do
  match body with
  | .vdecl x ty expr next =>
    let _ ← require (!env.used x.idx)
    let (value, rhs) ← reifyExpr env ty expr
    match value with
    | .word e =>
      let _ ← require (ty == .uint64)
      let (p, tail) ← reifyBody (env.addWord x.idx e) next
      return (p, s!"    let x_{x.idx}: u64 = {rhs};\n" ++ tail)
    | .test c =>
      let _ ← require (ty == .uint8)
      let (p, tail) ← reifyBody (env.addTest x.idx c) next
      return (p, s!"    let x_{x.idx}: u8 = {rhs};\n" ++ tail)
  | .ret arg =>
    let id ← argId arg
    let word ← env.words id
    return (.ret word, s!"    x_{id}\n")
  | .case tid x ty alts =>
    let _ ← require (tid.toString == "UInt8" && ty == .uint8 && alts.size == 2)
    let condition ← env.tests x.idx
    let mut falseBranch : Option Program := none
    let mut trueBranch : Option Program := none
    let mut text := "    match x_" ++ toString x.idx ++ " {\n"
    for alt in alts do
      match alt with
      | .ctor info branch =>
        let index := info.cidx
        let name := info.name.toString
        let _ ← require ((index == 0 && name == "Bool.false") ||
                         (index == 1 && name == "Bool.true"))
        let (program, rendered) ← reifyBody env branch
        if index == 0 then
          let _ ← require falseBranch.isNone
          falseBranch := some program
        else
          let _ ← require trueBranch.isNone
          trueBranch := some program
        text := text ++ "        " ++ toString index ++ " => {\n" ++ rendered ++ "        }\n"
      | .default _ => none
    let f ← falseBranch
    let t ← trueBranch
    text := text ++ "        _ => unreachable!(\"invalid Lean Bool tag\"),\n    }\n"
    return (.branch condition t f, text)
  | _ => none

/-- This is intentionally not a general IR translation. It rejects direct
calls, joins, RC effects, heap objects, non-UInt64 types and anything else
outside the existing modeled theorem. -/
private def reifyDecl (decl : IR.Decl) (rustName : String) :
    Option (Program × String) := do
  match decl with
  | .fdecl name params ret body _ =>
    let _ ← require (ret == .uint64 && !params.isEmpty)
    let _ ← require (rustName == "certified_scalar")
    let mut env : Bindings := {}
    let mut renderedParams := #[]
    for i in [:params.size] do
      let p := params[i]!
      let _ ← require (p.ty == .uint64 && !p.borrow && !env.used p.x.idx)
      env := env.addWord p.x.idx (.arg i)
      renderedParams := renderedParams.push s!"x_{p.x.idx}: u64"
    let (program, code) ← reifyBody env body
    let name := name.toString.replace "\n" "_"
    let name := name.replace "\r" "_"
    let expected :=
      s!"// Generated directly from Lean IR declaration: {name}\n" ++
      "#[allow(clippy::needless_return)]\n" ++
      "pub fn certified_scalar(" ++ String.intercalate ", " renderedParams.toList ++
      ") -> u64 {\n" ++ code ++ "}\n"
    return (program, expected)
  | _ => none

/-- The actual emitted string, an independent source-derived prediction, and
the syntax tree covered by the existing all-inputs proof. This structure is
constructed only after exact full-text equality. -/
structure Certificate where
  program : Program
  emitted : String
  expected : String
  exact : emitted = expected

theorem certified_model_refines (c : Certificate) (env : Nat → UInt64) :
    evalRustProgramSyntax (fun i => (env i).toNat) (lowerProgram c.program) =
      (evalActualProgram env c.program).toNat :=
  modeled_compiler_refines env c.program

/-- Reader is *actually invoked*. No reconstruction or substitute emitter
stands in for the real Rust FFI. All unsupported IR is refused here even when
the general, unproved backend can compile it. -/
def certify (root : Name) : CoreM Certificate := do
  let emitted ← NativeRust.compile root "certified_scalar"
  let some decl ← IR.findDecl root
    | throwError "certification refused: {root} has no compiler IR"
  let some (model, expected) := reifyDecl decl "certified_scalar"
    | throwError "certification refused: {root} is outside proved scalar IR"
  if h : emitted = expected then
    return { program := model, emitted, expected, exact := h }
  else
    throwError "certification refused: Reader output differs from independent scalar rendering for {root}"

end ReaderScalarCertificate

open Lean Elab Command

run_cmd do
  for root in #[`ScalarFixture.plus, `ScalarFixture.choose, `ScalarFixture.nested] do
    let certificate ← liftCoreM <| ReaderScalarCertificate.certify root
    unless certificate.emitted == certificate.expected do
      throwError "impossible certificate equality failure for {root}"
    logInfo m!"Reader exact-emission certificate passed: {root}"
  -- The general compiler can emit UInt64.sub, but the proved target grammar
  -- cannot certify it. A successful Reader emission must not widen the proof.
  let generalOutput ← liftCoreM <| NativeRust.compile `ScalarFixture.subtract "certified_scalar"
  unless generalOutput.contains "wrapping_sub" do
    throwError "negative fixture did not exercise supported Reader subtraction"
  let refused ← try
    let _ ← liftCoreM <| ReaderScalarCertificate.certify `ScalarFixture.subtract
    pure false
  catch _ =>
    pure true
  unless refused do
    throwError "unproved UInt64.sub incorrectly received a scalar certificate"
  logInfo "Reader scalar certificate correctly refused unsupported subtraction"
