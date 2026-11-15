import Lean
import ScalarOperationalRefinement
import NativeRust
import ScalarFixture
import ReaderScalarCertificate

/-!
# Operational semantics of a certified, straight-line original Lean IR fragment

The two judgments below run *actual Lean.IR.Expr* and *Lean.IR.FnBody*
constructors, not a copy of the reified WordExpr. Their operations are the
genuine pinned Lean UInt64 operations and their variable environments are
indexed by the actual compiler VarId. No Rust behavior is assumed.

A proof-producing reader returns a structural relation between those real IR
constructors and the already proved WordExpr/Program. This theorem is
parametric in all UInt64 inputs and in the length of the accepted straight-line
body. It does NOT yet cover branching, calls, ownership or rustc execution.
-/

open Lean
open NativeRustScalarRefinement

namespace ReaderIRSoundness

abbrev SymbolicEnv := Nat → Option WordExpr
abbrev SourceEnv := Nat → Option UInt64

def setVar {α : Type} (env : Nat → Option α) (id : Nat) (value : α) :
    Nat → Option α :=
  fun i => if i = id then some value else env i

/-- Independent source meaning: the original compiler-IR primitive spelling,
the original operand slots, and real Lean UInt64 arithmetic. -/
inductive ExprRuns (env : SourceEnv) : IR.Expr → UInt64 → Prop where
  | literal (n : Nat) :
      ExprRuns env (.lit (.num n)) (UInt64.ofNat n)
  | add (args : Array IR.Arg) (a b : IR.VarId) (u v : UInt64)
      (hsize : args.size = 2)
      (ha : args[0]? = some (.var a))
      (hb : args[1]? = some (.var b))
      (hu : env a.idx = some u)
      (hv : env b.idx = some v) :
      ExprRuns env (.fap `UInt64.add args) (u + v)
  | mul (args : Array IR.Arg) (a b : IR.VarId) (u v : UInt64)
      (hsize : args.size = 2)
      (ha : args[0]? = some (.var a))
      (hb : args[1]? = some (.var b))
      (hu : env a.idx = some u)
      (hv : env b.idx = some v) :
      ExprRuns env (.fap `UInt64.mul args) (u * v)

/-- A big-step source semantics over actual IR constructor nodes. -/
inductive BodyRuns : IR.FnBody → SourceEnv → UInt64 → Prop where
  | ret (env : SourceEnv) (id : IR.VarId) (value : UInt64)
      (h : env id.idx = some value) :
      BodyRuns (.ret (.var id)) env value
  | bind (env : SourceEnv) (id : IR.VarId) (expr : IR.Expr)
      (tail : IR.FnBody) (value result : UInt64)
      (hexpr : ExprRuns env expr value)
      (htail : BodyRuns tail (setVar env id.idx value) result) :
      BodyRuns (.vdecl id .uint64 expr tail) env result

/-- Independent syntax-directed relation between actual IR and model syntax.
The constructors enforce source name identity, operand positions and types. -/
inductive ExprMatches (env : SymbolicEnv) : IR.Expr → WordExpr → Prop where
  | literal (n : Nat) :
      ExprMatches env (.lit (.num n)) (.lit n)
  | add (args : Array IR.Arg) (a b : IR.VarId) (u v : WordExpr)
      (hsize : args.size = 2)
      (ha : args[0]? = some (.var a))
      (hb : args[1]? = some (.var b))
      (hu : env a.idx = some u)
      (hv : env b.idx = some v) :
      ExprMatches env (.fap `UInt64.add args) (.add u v)
  | mul (args : Array IR.Arg) (a b : IR.VarId) (u v : WordExpr)
      (hsize : args.size = 2)
      (ha : args[0]? = some (.var a))
      (hb : args[1]? = some (.var b))
      (hu : env a.idx = some u)
      (hv : env b.idx = some v) :
      ExprMatches env (.fap `UInt64.mul args) (.mul u v)

inductive BodyMatches : SymbolicEnv → IR.FnBody → Program → Prop where
  | ret (env : SymbolicEnv) (id : IR.VarId) (value : WordExpr)
      (h : env id.idx = some value) :
      BodyMatches env (.ret (.var id)) (.ret value)
  | bind (env : SymbolicEnv) (id : IR.VarId) (expr : IR.Expr) (tail : IR.FnBody)
      (value : WordExpr) (result : Program)
      (hexpr : ExprMatches env expr value)
      (htail : BodyMatches (setVar env id.idx value) tail result) :
      BodyMatches env (.vdecl id .uint64 expr tail) result

def EnvAgrees (sym : SymbolicEnv) (runtime : SourceEnv)
    (inputs : Nat → UInt64) : Prop :=
  ∀ i e, sym i = some e →
    runtime i = some (evalActualUInt64 inputs e)

theorem empty_agrees (inputs : Nat → UInt64) :
    EnvAgrees (fun _ => none) (fun _ => none) inputs := by
  intro i e h
  cases h

theorem set_agrees {sym : SymbolicEnv} {runtime : SourceEnv}
    {inputs : Nat → UInt64} (h : EnvAgrees sym runtime inputs)
    (id : Nat) (value : WordExpr) :
    EnvAgrees (setVar sym id value)
      (setVar runtime id (evalActualUInt64 inputs value)) inputs := by
  intro i e he
  by_cases hid : i = id
  · subst i
    simp only [setVar, ↓reduceIte] at he ⊢
    cases he
    rfl
  · have old : sym i = some e := by
      simpa only [setVar, if_neg hid] using he
    simpa only [setVar, if_neg hid] using h i e old

/-- An expression witness preserves the actual Lean arithmetic meaning,
for every consistent concrete environment, not only the CI input vectors. -/
theorem expr_sound {sym : SymbolicEnv} {expr : IR.Expr} {word : WordExpr}
    (h : ExprMatches sym expr word) (inputs : Nat → UInt64)
    (runtime : SourceEnv) (agree : EnvAgrees sym runtime inputs) :
    ExprRuns runtime expr (evalActualUInt64 inputs word) := by
  cases h with
  | literal n =>
      exact ExprRuns.literal n
  | add args a b u v hs ha hb hu hv =>
      exact ExprRuns.add args a b _ _ hs ha hb
        (agree a.idx u hu) (agree b.idx v hv)
  | mul args a b u v hs ha hb hu hv =>
      exact ExprRuns.mul args a b _ _ hs ha hb
        (agree a.idx u hu) (agree b.idx v hv)

/-- Compositional source-IR theorem: every witnessed sequence of real IR
bindings has exactly the value assigned by the proved source Program. -/
theorem body_sound {sym : SymbolicEnv} {body : IR.FnBody} {p : Program}
    (h : BodyMatches sym body p) :
    ∀ (inputs : Nat → UInt64) (runtime : SourceEnv),
      EnvAgrees sym runtime inputs →
        BodyRuns body runtime (evalActualProgram inputs p) := by
  induction h with
  | ret env id value hv =>
      intro inputs runtime agrees
      exact BodyRuns.ret runtime id _ (agrees id.idx value hv)
  | bind env id expr tail value result he ht ih =>
      intro inputs runtime agrees
      exact BodyRuns.bind runtime id expr tail _ _
        (expr_sound he inputs runtime agrees)
        (ih inputs (setVar runtime id.idx (evalActualUInt64 inputs value))
          (set_agrees agrees id.idx value))

structure WordWitness (sym : SymbolicEnv) (expr : IR.Expr) where
  word : WordExpr
  derivation : ExprMatches sym expr word

structure BodyWitness (sym : SymbolicEnv) (body : IR.FnBody) where
  program : Program
  derivation : BodyMatches sym body program

/-- A second, proof-producing scanner. Unlike the independent Rust renderer,
this scanner returns explicit constructors of BodyMatches; it cannot certify
an unrecognized instruction or an arbitrary primitive name. -/
private def wordExpr (sym : SymbolicEnv) (expr : IR.Expr) :
    Option (WordWitness sym expr) :=
  match expr with
  | .lit (.num n) =>
      some {word := .lit n, derivation := .literal n}
  | .fap name args =>
    if hs : args.size = 2 then
      match ha : args[0]? with
      | some (IR.Arg.var a) =>
        match hb : args[1]? with
        | some (IR.Arg.var b) =>
          match hu : sym a.idx with
          | some u =>
            match hv : sym b.idx with
            | some v =>
              if hn : name = `UInt64.add then
                some (WordWitness.mk (.add u v) (by
                  simpa only [hn] using
                    (ExprMatches.add args a b u v hs ha hb hu hv)))
              else if hn : name = `UInt64.mul then
                some (WordWitness.mk (.mul u v) (by
                  simpa only [hn] using
                    (ExprMatches.mul args a b u v hs ha hb hu hv)))
              else none
            | none => none
          | none => none
        | _ => none
      | _ => none
    else none
  | _ => none

private partial def straightBody (sym : SymbolicEnv) (body : IR.FnBody) :
    Option (BodyWitness sym body) :=
  match body with
  | .ret (.var id) =>
      match hv : sym id.idx with
      | some value => some {program := .ret value, derivation := .ret sym id value hv}
      | none => none
  | .vdecl id .uint64 expr tail =>
      match wordExpr sym expr with
      | some {word := value, derivation := hexpr} =>
          match straightBody (setVar sym id.idx value) tail with
          | some {program := p, derivation := htail} =>
              some {program := p, derivation := .bind sym id expr tail value p hexpr htail}
          | none => none
      | none => none
  | _ => none

def inputWords (a b : UInt64) : Nat → UInt64 :=
  fun n => if n = 0 then a else if n = 1 then b else 0

def initialSym (left right : Nat) : SymbolicEnv :=
  setVar (setVar (fun _ => none) left (.arg 0)) right (.arg 1)

def initialRuntime (left right : Nat) (a b : UInt64) : SourceEnv :=
  setVar (setVar (fun _ => none) left a) right b

theorem initial_agrees (left right : Nat) (a b : UInt64) :
    EnvAgrees (initialSym left right) (initialRuntime left right a b)
      (inputWords a b) := by
  exact set_agrees
    (set_agrees (empty_agrees (inputWords a b)) left (.arg 0))
    right (.arg 1)

/-- A certificate for a real original compiler body and its two UInt64
source parameter slots. No hand-transcribed scalar Program is accepted. -/
structure StraightCertificate where
  left : Nat
  right : Nat
  body : IR.FnBody
  program : Program
  matchIR : BodyMatches (initialSym left right) body program

/-- This accepts only a two-parameter original Lean IR fdecl with a UInt64
return and a proof-carrying straight-line body. The original Reader backend
has a wider support policy: it is not implicitly certified here. -/
def reifyDecl (decl : IR.Decl) : Option StraightCertificate := do
  match decl with
  | .fdecl _ params .uint64 body _ =>
      if params.size != 2 then none else
      let some p0 := params[0]? | none
      let some p1 := params[1]? | none
      if p0.ty != .uint64 || p1.ty != .uint64 ||
         p0.borrow || p1.borrow || p0.x.idx == p1.x.idx then
        none
      else
        let witness ← straightBody (initialSym p0.x.idx p1.x.idx) body
        some {left := p0.x.idx, right := p1.x.idx,
              body, program := witness.program, matchIR := witness.derivation}
  | _ => none

/-- For every pair of UInt64 inputs, the *actual Lean IR body* has the
source meaning of its proof-carrying reification. -/
theorem original_ir_refines (c : StraightCertificate) (a b : UInt64) :
    BodyRuns c.body (initialRuntime c.left c.right a b)
      (evalActualProgram (inputWords a b) c.program) := by
  exact body_sound c.matchIR (inputWords a b)
    (initialRuntime c.left c.right a b)
    (initial_agrees c.left c.right a b)

/-- Composition with the already proved target semantics. This is an actual
IR-to-modeled-target value theorem, not a rustc or ownership theorem. -/
theorem original_ir_target_refines (c : StraightCertificate) (a b : UInt64) :
    ∃ value,
      BodyRuns c.body (initialRuntime c.left c.right a b) value ∧
      evalRustProgramSyntax (fun i => (inputWords a b i).toNat)
        (lowerProgram c.program) = value.toNat := by
  refine ⟨evalActualProgram (inputWords a b) c.program,
    original_ir_refines c a b, ?_⟩
  exact modeled_compiler_refines (inputWords a b) c.program

/-- A combined certificate requires the independently produced source-IR
witness and Reader's byte-for-byte Rust source equality to reify the SAME
model program. The source-to-model theorem is kernel checked for all inputs. -/
structure LinkedCertificate where
  source : StraightCertificate
  emission : ReaderScalarCertificate.Certificate
  sameProgram : source.program = emission.program

theorem linked_reader_refines (c : LinkedCertificate) (a b : UInt64) :
    ∃ value,
      BodyRuns c.source.body
        (initialRuntime c.source.left c.source.right a b) value ∧
      evalRustProgramSyntax (fun i => (inputWords a b i).toNat)
        (lowerProgram c.emission.program) = value.toNat := by
  rw [← c.sameProgram]
  exact original_ir_target_refines c.source a b

end ReaderIRSoundness

open Lean Elab Command

run_cmd do
  let root := `ScalarFixture.plus
  let emitted ← liftCoreM <| ReaderScalarCertificate.certify root
  let some decl ← liftCoreM <| Lean.IR.findDecl root
    | throwError "original source IR not found: {root}"
  let some source := ReaderIRSoundness.reifyDecl decl
    | throwError "proof-producing original IR checker refused {root}"
  if h : source.program = emitted.program then
    let combined : ReaderIRSoundness.LinkedCertificate :=
      { source, emission := emitted, sameProgram := h }
    let _ := ReaderIRSoundness.linked_reader_refines combined
    logInfo "Original Lean IR operational semantics linked to actual Reader emission"
  else
    throwError "source IR witness disagrees with Reader's canonical target model"
