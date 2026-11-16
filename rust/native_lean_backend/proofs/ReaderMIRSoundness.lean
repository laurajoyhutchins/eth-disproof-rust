import ReaderRustStatement

/-!
A separate bounded operational model for the MIR CFG observed in rustc 1.99.1.
MIR has numbered blocks, temporaries, statements, and explicit successor edges.
The source Rust statement proof does not by itself establish this relation.

Everything in this file is generic over any graph using the restricted opcode
grammar. The subsequent live-MIR decoder must reject all other constructs.
The semantics of the real rustc printer and LLVM remain outside this theorem.
-/

open Lean
open NativeRustScalarRefinement
open ReaderIRSoundness

namespace ReaderMIR

inductive Op where
  | literal : Nat → Nat → Op
  | copy : Nat → Nat → Op
  | add : Nat → Nat → Nat → Op
  | mul : Nat → Nat → Nat → Op
  | eq : Nat → Nat → Nat → Op
  | lt : Nat → Nat → Nat → Op
  | le : Nat → Nat → Nat → Op
  | boolToTag : Nat → Nat → Op
  deriving Repr, DecidableEq

inductive Exit where
  | ret
  | goto : Nat → Exit
  | switch : Nat → Nat → Nat → Nat → Exit
  | panic
  deriving Repr, DecidableEq

structure Block where
  operations : List Op
  exit : Exit
  deriving Repr, DecidableEq

abbrev Graph := List (Nat × Block)

def lookup : Graph → Nat → Option Block
  | [], _ => none
  | (i, b) :: rest, target =>
      if i == target then some b else lookup rest target

def trapEdge (graph : Graph) (target : Nat) : Bool :=
  match lookup graph target with
  | some ⟨[], .panic⟩ => true
  | some ⟨[], .goto next⟩ =>
      match lookup graph next with
      | some ⟨[], .panic⟩ => true
      | _ => false
  | _ => false

structure Symbolic where
  words : Nat → Option WordExpr
  flags : Nat → Option Condition
  tags : Nat → Option Condition

structure Concrete where
  words : Nat → Option Nat
  flags : Nat → Option Bool
  tags : Nat → Option Nat

def put {α : Type} (m : Nat → Option α) (id : Nat) (value : α) :
    Nat → Option α :=
  fun i => if i = id then some value else m i

theorem map_put {α β : Type} (f : α → β) (m : Nat → Option α)
    (id : Nat) (v : α) :
    (fun i => (put m id v i).map f) =
      put (fun i => (m i).map f) id (f v) := by
  funext i
  by_cases hi : i = id
  · simp [put, hi]
  · simp [put, hi]

def materialize (inputs : Nat → Nat) (s : Symbolic) : Concrete :=
  { words := fun i => (s.words i).map (evalRustWord inputs)
    flags := fun i => (s.flags i).map (evalRustCondition inputs)
    tags := fun i => (s.tags i).map
      (fun c => rustBoolTag (evalRustCondition inputs c)) }

def symStep (s : Symbolic) : Op → Option Symbolic
  | .literal id n =>
      some { s with words := put s.words id (.lit n) }
  | .copy id src => do
      let e ← s.words src
      some { s with words := put s.words id e }
  | .add id a b => do
      let u ← s.words a
      let v ← s.words b
      some { s with words := put s.words id (.add u v) }
  | .mul id a b => do
      let u ← s.words a
      let v ← s.words b
      some { s with words := put s.words id (.mul u v) }
  | .eq id a b => do
      let u ← s.words a
      let v ← s.words b
      some { s with flags := put s.flags id (.eq u v) }
  | .lt id a b => do
      let u ← s.words a
      let v ← s.words b
      some { s with flags := put s.flags id (.lt u v) }
  | .le id a b => do
      let u ← s.words a
      let v ← s.words b
      some { s with flags := put s.flags id (.le u v) }
  | .boolToTag id src => do
      let c ← s.flags src
      some { s with tags := put s.tags id c }

def realStep (r : Concrete) : Op → Option Concrete
  | .literal id n =>
      some { r with words := put r.words id (n % modulus) }
  | .copy id src => do
      let v ← r.words src
      some { r with words := put r.words id v }
  | .add id a b => do
      let u ← r.words a
      let v ← r.words b
      some { r with words := put r.words id ((u + v) % modulus) }
  | .mul id a b => do
      let u ← r.words a
      let v ← r.words b
      some { r with words := put r.words id ((u * v) % modulus) }
  | .eq id a b => do
      let u ← r.words a
      let v ← r.words b
      some { r with flags := put r.flags id (decide (u = v)) }
  | .lt id a b => do
      let u ← r.words a
      let v ← r.words b
      some { r with flags := put r.flags id (decide (u < v)) }
  | .le id a b => do
      let u ← r.words a
      let v ← r.words b
      some { r with flags := put r.flags id (decide (u ≤ v)) }
  | .boolToTag id src => do
      let v ← r.flags src
      some { r with tags := put r.tags id (rustBoolTag v) }

theorem step_sound (s s' : Symbolic) (op : Op) (inputs : Nat → Nat)
    (h : symStep s op = some s') :
    realStep (materialize inputs s) op =
      some (materialize inputs s') := by
  cases op with
  | literal id n =>
      simp [symStep] at h
      subst s'
      simp [realStep, materialize, map_put, evalRustWord]
  | copy id src =>
      cases he : s.words src with
      | none => simp [symStep, he] at h
      | some e =>
          simp [symStep, he] at h
          subst s'
          simp [realStep, materialize, he, map_put]
  | add id a b =>
      cases ha : s.words a with
      | none => simp [symStep, ha] at h
      | some u =>
          cases hb : s.words b with
          | none => simp [symStep, ha, hb] at h
          | some v =>
              simp [symStep, ha, hb] at h
              subst s'
              simp [realStep, materialize, ha, hb, map_put, evalRustWord]
  | mul id a b =>
      cases ha : s.words a with
      | none => simp [symStep, ha] at h
      | some u =>
          cases hb : s.words b with
          | none => simp [symStep, ha, hb] at h
          | some v =>
              simp [symStep, ha, hb] at h
              subst s'
              simp [realStep, materialize, ha, hb, map_put, evalRustWord]
  | eq id a b =>
      cases ha : s.words a with
      | none => simp [symStep, ha] at h
      | some u =>
          cases hb : s.words b with
          | none => simp [symStep, ha, hb] at h
          | some v =>
              simp [symStep, ha, hb] at h
              subst s'
              simp [realStep, materialize, ha, hb, map_put, evalRustCondition]
  | lt id a b =>
      cases ha : s.words a with
      | none => simp [symStep, ha] at h
      | some u =>
          cases hb : s.words b with
          | none => simp [symStep, ha, hb] at h
          | some v =>
              simp [symStep, ha, hb] at h
              subst s'
              simp [realStep, materialize, ha, hb, map_put, evalRustCondition]
  | le id a b =>
      cases ha : s.words a with
      | none => simp [symStep, ha] at h
      | some u =>
          cases hb : s.words b with
          | none => simp [symStep, ha, hb] at h
          | some v =>
              simp [symStep, ha, hb] at h
              subst s'
              simp [realStep, materialize, ha, hb, map_put, evalRustCondition]
  | boolToTag id src =>
      cases hc : s.flags src with
      | none => simp [symStep, hc] at h
      | some c =>
          simp [symStep, hc] at h
          subst s'
          simp [realStep, materialize, hc, map_put]

def symOps : List Op → Symbolic → Option Symbolic
  | [], s => some s
  | op :: tail, s => do
      let next ← symStep s op
      symOps tail next

def realOps : List Op → Concrete → Option Concrete
  | [], r => some r
  | op :: tail, r => do
      let next ← realStep r op
      realOps tail next

theorem ops_sound (ops : List Op) (s s' : Symbolic)
    (inputs : Nat → Nat) (h : symOps ops s = some s') :
    realOps ops (materialize inputs s) =
      some (materialize inputs s') := by
  induction ops generalizing s with
  | nil =>
      simp [symOps] at h
      subst s'
      rfl
  | cons op tail ih =>
      cases hs : symStep s op with
      | none => simp [symOps, hs] at h
      | some mid =>
          have htail : symOps tail mid = some s' := by
            simpa [symOps, hs] using h
          simpa [realOps, step_sound s mid op inputs hs] using
            (ih mid htail)

def symRun (fuel : Nat) (graph : Graph) (pc : Nat)
    (s : Symbolic) : Option Program :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      let block ← lookup graph pc
      let state ← symOps block.operations s
      match block.exit with
      | .ret =>
          let value ← state.words 0
          some (.ret value)
      | .goto next => symRun fuel graph next state
      | .switch tag falsePc truePc otherwisePc =>
          if !trapEdge graph otherwisePc then none else
          let condition ← state.tags tag
          let trueResult ← symRun fuel graph truePc state
          let falseResult ← symRun fuel graph falsePc state
          some (.branch condition trueResult falseResult)
      | .panic => none

def realRun (fuel : Nat) (graph : Graph) (pc : Nat)
    (r : Concrete) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      let block ← lookup graph pc
      let state ← realOps block.operations r
      match block.exit with
      | .ret => state.words 0
      | .goto next => realRun fuel graph next state
      | .switch tag falsePc truePc _ =>
          let value ← state.tags tag
          if value == 1 then realRun fuel graph truePc state
          else if value == 0 then realRun fuel graph falsePc state
          else none
      | .panic => none

theorem run_sound (fuel : Nat) (graph : Graph) (pc : Nat)
    (s : Symbolic) (p : Program) (inputs : Nat → Nat)
    (h : symRun fuel graph pc s = some p) :
    realRun fuel graph pc (materialize inputs s) =
      some (evalRustProgram inputs p) := by
  induction fuel generalizing pc s p with
  | zero =>
      simp [symRun] at h
  | succ fuel ih =>
      cases hb : lookup graph pc with
      | none => simp [symRun, hb] at h
      | some block =>
          cases hs : symOps block.operations s with
          | none => simp [symRun, hb, hs] at h
          | some after =>
              have hreal := ops_sound block.operations s after inputs hs
              cases ht : block.exit with
              | ret =>
                  cases hv : after.words 0 with
                  | none => simp [symRun, hb, hs, ht, hv] at h
                  | some e =>
                      simp [symRun, hb, hs, ht, hv] at h
                      subst p
                      simp [realRun, hb, hreal, ht, materialize, hv,
                        evalRustProgram]
              | goto next =>
                  have hchild : symRun fuel graph next after = some p := by
                    simpa [symRun, hb, hs, ht] using h
                  simpa [realRun, hb, hreal, ht] using
                    (ih next after p hchild)
              | switch tag falsePc truePc other =>
                  by_cases htrap : trapEdge graph other = true
                  · cases hc : after.tags tag with
                    | none => simp [symRun, hb, hs, ht, htrap, hc] at h
                    | some cond =>
                        cases htrue : symRun fuel graph truePc after with
                        | none => simp [symRun, hb, hs, ht, htrap, hc, htrue] at h
                        | some tp =>
                            cases hfalse : symRun fuel graph falsePc after with
                            | none =>
                                simp [symRun, hb, hs, ht, htrap, hc, htrue, hfalse] at h
                            | some fp =>
                                simp [symRun, hb, hs, ht, htrap,
                                  hc, htrue, hfalse] at h
                                subst p
                                have ht' := ih truePc after tp htrue
                                have hf' := ih falsePc after fp hfalse
                                cases hcond : evalRustCondition inputs cond with
                                | true =>
                                    simpa [realRun, hb, hreal, ht, materialize,
                                      hc, hcond, rustBoolTag, evalRustProgram] using ht'
                                | false =>
                                    simpa [realRun, hb, hreal, ht, materialize,
                                      hc, hcond, rustBoolTag, evalRustProgram] using hf'
                  · have hnot : trapEdge graph other = false := by
                      cases ht2 : trapEdge graph other <;> simp_all
                    simp [symRun, hb, hs, ht, hnot] at h
              | panic =>
                  simp [symRun, hb, hs, ht] at h

def sourceSymbols : Symbolic :=
  { words := put (put (fun _ => none) 1 (.arg 0)) 2 (.arg 1)
    flags := fun _ => none
    tags := fun _ => none }

def initialRegisters (a b : UInt64) : Concrete :=
  materialize (fun i => (ReaderIRSoundness.inputWords a b i).toNat)
    sourceSymbols

theorem certified_mir_refines (graph : Graph) (fuel : Nat)
    (p : Program) (h : symRun fuel graph 0 sourceSymbols = some p)
    (a b : UInt64) :
    realRun fuel graph 0 (initialRegisters a b) =
      some ((evalActualProgram (ReaderIRSoundness.inputWords a b) p).toNat) := by
  have hm := run_sound fuel graph 0 sourceSymbols p
    (fun i => (ReaderIRSoundness.inputWords a b i).toNat) h
  have he := modeled_compiler_refines (ReaderIRSoundness.inputWords a b) p
  rw [lowerProgram_correct] at he
  exact hm.trans (congrArg some he)

end ReaderMIR

#print axioms ReaderMIR.step_sound
#print axioms ReaderMIR.ops_sound
#print axioms ReaderMIR.run_sound
#print axioms ReaderMIR.certified_mir_refines
