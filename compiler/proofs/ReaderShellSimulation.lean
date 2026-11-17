import Lean

/-!
# A source-credit / physical-reference-count simulation for one Box shell

This is a deliberately small, executable transition-system proof. It is not
a theorem about Lean 4's actual allocator or about all original compiler IR.

There are TWO independent step definitions:
* `sourceStep`: abstract owned credits and borrowed projections;
* `physicalStep`: reference counts, physical slots, and shell liveness.

`represent` relates them, including the already-owned field references:
  childRC = projectedCredits + (if childField then 1 else 0)
  oldStampRC = oldStampExternal + (if old stamp still occupies slot then 1 else 0)

The `stampDec` operation consumes the existing field credit; it does not
increment a projection. The `shellDel` operation *moves* the child field
credit to the existing borrowed handle and destroys only the parent shell.
A join transfers its source name but changes neither physical RC nor the
allocation identity.

The model's shell deletion also requires zero independently retained child\ncredits, matching the physical adapter's child-RC-equals-one guard.\n\nThe real implementation and its pinned Lean C oracle live in
compiler/runtime/lean-c; this model has not yet been linked to their code
by a compiler or FFI refinement theorem.
-/

namespace ReaderShellSimulation

inductive StampSlot where
  | old | spent | fresh
  deriving Repr, DecidableEq

structure Source where
  parentCredits : Nat
  childField : Bool
  childProjectionCredits : Nat
  borrowedChild : Bool
  stampSlot : StampSlot
  oldStampExternal : Nat
  observedUnique : Bool
  ownerName : Nat
  deriving Repr, DecidableEq

structure Physical where
  parentRC : Nat
  childRC : Nat
  oldStampRC : Nat
  shellLive : Bool
  childField : Bool
  borrowedChild : Bool
  stampSlot : StampSlot
  observedUnique : Bool
  deriving Repr, DecidableEq

def credit (b : Bool) : Nat := if b then 1 else 0

/-- This representation relation accounts for the *existing* credit in
each constructor field. A Rust Rc alias is deliberately absent. -/
def represent (s : Source) : Physical :=
  { parentRC := s.parentCredits
    childRC := s.childProjectionCredits + credit s.childField
    oldStampRC := s.oldStampExternal + credit (s.stampSlot == .old)
    shellLive := s.parentCredits != 0
    childField := s.childField
    borrowedChild := s.borrowedChild
    stampSlot := s.stampSlot
    observedUnique := s.observedUnique }

/-- A complete physical relation is stronger than output-value equality.
The join's `ownerName` is not a heap allocation ID. -/
def Agrees (s : Source) (p : Physical) : Prop := p = represent s

inductive Instruction where
  | borrowChild
  | inspectSharing
  | retainChild
  | retainParent
  | releaseSharedParent
  | stampDec
  | jumpOwned
  | setFreshStamp
  | shellDel
  | releaseProjectedChild
  deriving Repr, DecidableEq

/-- Source ledger transitions. An invalid or unsupported ownership
operation refuses instead of inventing a credit. -/
def sourceStep (s : Source) : Instruction → Option Source
  | .borrowChild =>
      if s.parentCredits == 0 || !s.childField then none
      else some { s with borrowedChild := true }
  | .inspectSharing =>
      if s.parentCredits == 0 then none
      else some { s with observedUnique := s.parentCredits == 1 }
  | .retainChild =>
      if s.parentCredits == 0 || !s.childField || !s.borrowedChild then none
      else some { s with childProjectionCredits := s.childProjectionCredits + 1 }
  | .retainParent =>
      if s.parentCredits == 0 then none
      else some { s with parentCredits := s.parentCredits + 1, observedUnique := false }
  | .releaseSharedParent =>
      if s.parentCredits <= 1 then none
      else some { s with parentCredits := s.parentCredits - 1, observedUnique := false }
  | .stampDec =>
      if !s.observedUnique || s.parentCredits != 1 || s.stampSlot != .old then none
      else some { s with stampSlot := .spent }
  | .jumpOwned =>
      if s.parentCredits == 0 then none
      else some { s with ownerName := s.ownerName + 1 }
  | .setFreshStamp =>
      if !s.observedUnique || s.parentCredits != 1 || s.stampSlot != .spent then none
      else some { s with stampSlot := .fresh }
  | .shellDel =>
      if !s.observedUnique || s.parentCredits != 1 || !s.childField ||
         !s.borrowedChild || s.stampSlot == .old ||
         s.childProjectionCredits != 0 then none
      else some { s with
        parentCredits := 0
        childField := false
        childProjectionCredits := s.childProjectionCredits + 1 }
  | .releaseProjectedChild =>
      if s.childField || s.childProjectionCredits == 0 then none
      else some { s with childProjectionCredits := s.childProjectionCredits - 1 }

/-- Independent physical transition rules. Notice `stampDec` acts on
oldStampRC; `shellDel` does NOT decrement childRC. -/
def physicalStep (p : Physical) : Instruction → Option Physical
  | .borrowChild =>
      if p.parentRC == 0 || !p.childField then none
      else some { p with borrowedChild := true }
  | .inspectSharing =>
      if p.parentRC == 0 then none
      else some { p with observedUnique := p.parentRC == 1 }
  | .retainChild =>
      if p.parentRC == 0 || !p.childField || !p.borrowedChild then none
      else some { p with childRC := p.childRC + 1 }
  | .retainParent =>
      if p.parentRC == 0 then none
      else some { p with parentRC := p.parentRC + 1, observedUnique := false }
  | .releaseSharedParent =>
      if p.parentRC <= 1 then none
      else some { p with parentRC := p.parentRC - 1, observedUnique := false }
  | .stampDec =>
      if !p.observedUnique || p.parentRC != 1 || p.stampSlot != .old ||
         p.oldStampRC == 0 then none
      else some { p with stampSlot := .spent, oldStampRC := p.oldStampRC - 1 }
  | .jumpOwned =>
      if p.parentRC == 0 then none else some p
  | .setFreshStamp =>
      if !p.observedUnique || p.parentRC != 1 || p.stampSlot != .spent then none
      else some { p with stampSlot := .fresh }
  | .shellDel =>
      if !p.observedUnique || p.parentRC != 1 || !p.childField ||
         !p.borrowedChild || p.stampSlot == .old || p.childRC != 1 then none
      else some { p with parentRC := 0, shellLive := false, childField := false }
  | .releaseProjectedChild =>
      if p.childField || p.childRC == 0 then none
      else some { p with childRC := p.childRC - 1 }

/-- The restricted source and physical instructions commute with the
representation map, including *refusals*. The right side is not the
definition of `physicalStep`; it is a property of the two machines. -/
theorem step_simulation (s : Source) (instr : Instruction) :
    physicalStep (represent s) instr =
      (sourceStep s instr).map represent := by
  cases instr with
  | borrowChild =>
      simp [sourceStep, physicalStep, represent] <;>
        split_ifs <;> simp_all [represent]
  | inspectSharing =>
      simp [sourceStep, physicalStep, represent] <;>
        split_ifs <;> simp_all [represent]
  | retainChild =>
      simp [sourceStep, physicalStep, represent, credit] <;>
        split_ifs <;>
        simp_all [represent, credit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | retainParent =>
      simp [sourceStep, physicalStep, represent] <;>
        split_ifs <;> simp_all [represent] <;> omega
  | releaseSharedParent =>
      simp [sourceStep, physicalStep, represent] <;>
        split_ifs <;> simp_all [represent] <;> omega
  | stampDec =>
      cases hs : s.stampSlot <;>
        simp [sourceStep, physicalStep, represent, credit, hs] <;>
        split_ifs <;> simp_all [represent, credit] <;> omega
  | jumpOwned =>
      simp [sourceStep, physicalStep, represent] <;>
        split_ifs <;> simp_all [represent]
  | setFreshStamp =>
      cases hs : s.stampSlot <;>
        simp [sourceStep, physicalStep, represent, credit, hs] <;>
        split_ifs <;> simp_all [represent, credit]
  | shellDel =>
      cases hfield : s.childField <;>
        cases hs : s.stampSlot <;>
        cases hproj : s.childProjectionCredits <;>
        simp [sourceStep, physicalStep, represent, credit,
              hfield, hs, hproj] <;>
        split_ifs <;> simp_all [represent, credit, hfield, hs, hproj] <;> omega
  | releaseProjectedChild =>
      cases hfield : s.childField <;>
        simp [sourceStep, physicalStep, represent, credit, hfield] <;>
        split_ifs <;> simp_all [represent, credit, hfield] <;> omega


def runSource : List Instruction → Source → Option Source
  | [], s => some s
  | x :: xs, s => do
      let next ← sourceStep s x
      runSource xs next

def runPhysical : List Instruction → Physical → Option Physical
  | [], p => some p
  | x :: xs, p => do
      let next ← physicalStep p x
      runPhysical xs next

/-- All finite admitted traces in this *specified restricted machine*
preserve the simulation, not just a fixed number of sample transitions. -/
theorem trace_simulation (steps : List Instruction) (s : Source) :
    runPhysical steps (represent s) =
      (runSource steps s).map represent := by
  induction steps generalizing s with
  | nil => rfl
  | cons step rest ih =>
      simp only [runPhysical, runSource]
      rw [step_simulation]
      cases hs : sourceStep s step with
      | none => simp [hs]
      | some next =>
          simp [hs]
          exact ih next

def initial (extraStampOwners : Nat) : Source :=
  { parentCredits := 1
    childField := true
    childProjectionCredits := 0
    borrowedChild := false
    stampSlot := .old
    oldStampExternal := extraStampOwners
    observedUnique := false
    ownerName := 1 }

/-- Unique branch: the old stamp's credit is released, a join renames
the parent owner, and shell deletion transfers the child field credit
into the existing projection without incrementing the child's count. -/
def deleteTrace : List Instruction :=
  [.borrowChild, .inspectSharing, .stampDec, .jumpOwned, .shellDel]

/-- Unique reuse branch: the released old-stamp slot is replaced without
recursively releasing that old stamp again. -/
def reuseTrace : List Instruction :=
  [.borrowChild, .inspectSharing, .stampDec, .jumpOwned, .setFreshStamp]

theorem source_delete_trace (external : Nat) :
    runSource deleteTrace (initial external) =
      some { initial external with
        parentCredits := 0
        borrowedChild := true
        childField := false
        childProjectionCredits := 1
        stampSlot := .spent
        observedUnique := true
        ownerName := 2 } := by rfl

theorem physical_delete_trace (external : Nat) :
    runPhysical deleteTrace (represent (initial external)) =
      some { represent (initial external) with
        parentRC := 0
        childRC := 1
        oldStampRC := external
        shellLive := false
        borrowedChild := true
        childField := false
        stampSlot := .spent
        observedUnique := true } := by
  rw [trace_simulation, source_delete_trace]
  rfl

theorem physical_reuse_trace (external : Nat) :
    runPhysical reuseTrace (represent (initial external)) =
      some { represent (initial external) with
        parentRC := 1
        childRC := 1
        oldStampRC := external
        borrowedChild := true
        stampSlot := .fresh
        observedUnique := true } := by
  rw [trace_simulation]
  rfl

/-- An unspent old stamp is a hard refusal: a shell-only deletion cannot
erase its existing field credit. -/
def uniqueBeforeStampDec (external : Nat) : Source :=
  { (initial external) with borrowedChild := true, observedUnique := true }

theorem no_del_before_stamp_release (external : Nat) :
    sourceStep (uniqueBeforeStampDec external) .shellDel = none := rfl

def sharedBeforeStampDec (external : Nat) : Source :=
  { (initial external) with parentCredits := 2, observedUnique := false }

theorem no_stamp_release_on_shared_parent (external : Nat) :
    sourceStep (sharedBeforeStampDec external) .stampDec = none := rfl

/-- A wrong implementation that recursively decrements the child during
shell deletion violates the representation relation even when its
returned data values happen to match. -/
def incorrectRecursiveDel (p : Physical) : Physical :=
  { p with parentRC := 0, shellLive := false, childField := false,
    childRC := p.childRC - 1 }

def beforeDel (external : Nat) : Source :=
  { (initial external) with stampSlot := .spent,
    borrowedChild := true, observedUnique := true }

def afterDel (external : Nat) : Source :=
  { (initial external) with parentCredits := 0,
    stampSlot := .spent, childField := false,
    childProjectionCredits := 1, borrowedChild := true,
    observedUnique := true }

theorem recursive_delete_is_not_shell_delete (external : Nat) :
    incorrectRecursiveDel (represent (beforeDel external)) ≠
      represent (afterDel external) := by
  intro h
  have hc := congrArg Physical.childRC h
  simp [incorrectRecursiveDel, represent, beforeDel, afterDel,
    initial, credit] at hc


end ReaderShellSimulation

#print axioms ReaderShellSimulation.step_simulation
#print axioms ReaderShellSimulation.trace_simulation
#print axioms ReaderShellSimulation.source_delete_trace
#print axioms ReaderShellSimulation.physical_delete_trace
#print axioms ReaderShellSimulation.physical_reuse_trace
#print axioms ReaderShellSimulation.no_del_before_stamp_release
#print axioms ReaderShellSimulation.no_stamp_release_on_shared_parent
#print axioms ReaderShellSimulation.recursive_delete_is_not_shell_delete
