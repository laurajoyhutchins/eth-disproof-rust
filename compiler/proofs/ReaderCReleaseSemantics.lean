import Lean

/-!
# Selected pinned Lean C release branches and owned heap stamps

Source: leanprover/lean4 v4.34.1 src/include/lean/lean.h:
inc_ref_n (663-682), dec_ref (691-700), ctor_set (820-823),
del_object (560-564). src/runtime/object.cpp:
recursive deletion worklist (334-345), dec_ref_cold (467-487).

This is an executable FORMAL MODEL OF SELECTED C BRANCHES, not a
verified semantics of their C++ implementations. Real pinned C calls
are independently measured by the native trace oracle.

A constructor field owns a reference. lean_ctor_set merely writes
its pointer; it does not implicitly increment or release references.
-/

namespace ReaderCReleaseSemantics

inductive StampSlot where
  | old | spent | fresh
  deriving Repr, DecidableEq

inductive Op where
  | borrowChild | decOld | incFresh | storeFresh
  | incChild | decParent | decLastChild | shellDel
  deriving Repr, DecidableEq

/-- Source ledger: parent credits, independently retained child credits,
external stamp owners, and old/fresh field or pending credits. -/
structure Source where
  parentCredits : Nat
  childField : Bool
  extraChild : Nat
  oldExternal : Nat
  freshExternal : Nat
  stampSlot : StampSlot
  freshPending : Bool
  childBorrowed : Bool
  deriving Repr, DecidableEq

/-- Selected physical C branch footprint. A zero RC after final
release is a LOGICAL TOMBSTONE, never a read from a freed pointer. -/
structure Physical where
  parentRC : Nat
  childRC : Nat
  oldRC : Nat
  freshRC : Nat
  childField : Bool
  stampSlot : StampSlot
  freshPending : Bool
  childBorrowed : Bool
  deriving Repr, DecidableEq

def credit (b : Bool) : Nat := if b then 1 else 0

/-- Dead constructors no longer own stamp-field credits. A slot tag on a
tombstone is historical bookkeeping, not a live reference. -/
def liveFieldCredit (s : Source) (slot : StampSlot) : Nat :=
  credit (s.parentCredits != 0 && s.stampSlot == slot)

def freshCredit (s : Source) : Nat :=
  liveFieldCredit s .fresh + credit s.freshPending

def represent (s : Source) : Physical :=
  { parentRC := s.parentCredits
    childRC := s.extraChild + credit s.childField
    oldRC := s.oldExternal + liveFieldCredit s .old
    freshRC := s.freshExternal + freshCredit s
    childField := s.childField
    stampSlot := s.stampSlot
    freshPending := s.freshPending
    childBorrowed := s.childBorrowed }

/-- Credit accounting, independent of physical branch implementation. -/
def sourceStep (s : Source) : Op → Option Source
  | .borrowChild =>
      if s.parentCredits == 0 || !s.childField then none
      else some { s with childBorrowed := true }
  | .decOld =>
      if s.parentCredits != 1 || s.stampSlot != .old || s.oldExternal == 0 then none
      else some { s with stampSlot := .spent }
  | .incFresh =>
      if s.parentCredits != 1 || s.stampSlot != .spent ||
         s.freshPending || s.freshExternal == 0 then none
      else some { s with freshPending := true }
  | .storeFresh =>
      if s.parentCredits != 1 || s.stampSlot != .spent || !s.freshPending then none
      else some { s with stampSlot := .fresh, freshPending := false }
  | .incChild =>
      if s.parentCredits == 0 || !s.childField then none
      else some { s with extraChild := s.extraChild + 1 }
  | .decParent =>
      if s.parentCredits == 0 then none
      else if s.parentCredits > 1 then
        some { s with parentCredits := s.parentCredits - 1 }
      else if s.stampSlot == .spent || s.freshPending || !s.childField then none
      else some { s with parentCredits := 0, childField := false }
  | .decLastChild =>
      if s.childField || s.extraChild != 1 then none
      else some { s with extraChild := 0 }
  | .shellDel =>
      if s.parentCredits != 1 || !s.childField || !s.childBorrowed ||
         s.stampSlot != .spent || s.freshPending || s.extraChild != 0 then none
      else some { s with parentCredits := 0, childField := false, extraChild := 1 }

/-- Separately specified selected branches of Lean C. Last-parent dec
uses the recursive constructor field destructor; shell del does not. -/
def cStep (p : Physical) : Op → Option Physical
  | .borrowChild =>
      if p.parentRC == 0 || !p.childField then none
      else some { p with childBorrowed := true }
  | .decOld =>
      if p.parentRC != 1 || p.stampSlot != .old || p.oldRC <= 1 then none
      else some { p with oldRC := p.oldRC - 1, stampSlot := .spent }
  | .incFresh =>
      if p.parentRC != 1 || p.stampSlot != .spent ||
         p.freshPending || p.freshRC == 0 then none
      else some { p with freshRC := p.freshRC + 1, freshPending := true }
  | .storeFresh =>
      if p.parentRC != 1 || p.stampSlot != .spent || !p.freshPending then none
      else some { p with stampSlot := .fresh, freshPending := false }
  | .incChild =>
      if p.parentRC == 0 || !p.childField || p.childRC == 0 then none
      else some { p with childRC := p.childRC + 1 }
  | .decParent =>
      if p.parentRC == 0 then none
      else if p.parentRC > 1 then
        some { p with parentRC := p.parentRC - 1 }
      else if p.stampSlot == .spent || p.freshPending ||
          !p.childField || p.childRC == 0 ||
          (p.stampSlot == .old && p.oldRC == 0) ||
          (p.stampSlot == .fresh && p.freshRC == 0) then none
      else some { p with
        parentRC := 0
        childRC := p.childRC - 1
        oldRC := if p.stampSlot == .old then p.oldRC - 1 else p.oldRC
        freshRC := if p.stampSlot == .fresh then p.freshRC - 1 else p.freshRC
        childField := false }
  | .decLastChild =>
      if p.childField || p.childRC != 1 then none
      else some { p with childRC := 0 }
  | .shellDel =>
      if p.parentRC != 1 || !p.childField || !p.childBorrowed ||
         p.stampSlot != .spent || p.freshPending || p.childRC != 1 then none
      else some { p with parentRC := 0, childField := false }

theorem old_stamp_credit_identity (s : Source) :
    (represent s).oldRC =
      s.oldExternal + liveFieldCredit s .old := rfl

theorem fresh_stamp_credit_identity (s : Source) :
    (represent s).freshRC = s.freshExternal + freshCredit s := rfl

/-- All eight modeled operations commute with the source-credit representation,
including refused steps. This is about two explicit Lean models, not the C++
runtime implementation. -/
set_option maxHeartbeats 2000000 in
theorem cStep_represent (s : Source) (op : Op) :
    cStep (represent s) op = (sourceStep s op).map represent := by
  cases s with
  | mk parentCredits childField extraChild oldExternal freshExternal stampSlot freshPending childBorrowed =>
    cases op <;> cases stampSlot <;> cases childField <;>
      cases freshPending <;> cases childBorrowed <;>
      simp [sourceStep, cStep, represent, liveFieldCredit, freshCredit, credit] <;>
      split_ifs <;> simp_all <;> omega

/-- The C branch for field replacement changes NO physical RC.
The incoming owned credit was already acquired in incFresh. -/
theorem store_fresh_does_not_increment (p : Physical)
    (h : p.parentRC = 1) (hs : p.stampSlot = .spent)
    (hp : p.freshPending = true) :
    (cStep p .storeFresh).map Physical.freshRC = some p.freshRC := by
  simp [cStep, h, hs, hp]

theorem shell_del_preserves_child_rc (p : Physical)
    (h : p.parentRC = 1) (hc : p.childField = true)
    (hb : p.childBorrowed = true) (hs : p.stampSlot = .spent)
    (hp : p.freshPending = false) (hr : p.childRC = 1) :
    (cStep p .shellDel).map Physical.childRC = some p.childRC := by
  simp [cStep, h, hc, hb, hs, hp, hr]

/-- Actual memory is freed; zero here is a model tombstone, not a
valid post-free memory read. -/
theorem last_parent_release_drops_unretained_child (p : Physical)
    (h : p.parentRC = 1) (hc : p.childField = true)
    (hr : p.childRC = 1) (hs : p.stampSlot = .old)
    (hp : p.freshPending = false) (ho : p.oldRC > 0) :
    (cStep p .decParent).map Physical.childRC = some 0 := by
  have hn : p.oldRC ≠ 0 := Nat.ne_of_gt ho
  simp [cStep, h, hc, hr, hs, hp, hn]

theorem last_parent_release_preserves_retained_child (p : Physical)
    (h : p.parentRC = 1) (hc : p.childField = true)
    (hr : p.childRC = 2) (hs : p.stampSlot = .fresh)
    (hp : p.freshPending = false) (hf : p.freshRC > 0) :
    (cStep p .decParent).map Physical.childRC = some 1 := by
  have hn : p.freshRC ≠ 0 := Nat.ne_of_gt hf
  simp [cStep, h, hc, hr, hs, hp, hn]

theorem last_parent_release_fresh_stamp (p : Physical)
    (h : p.parentRC = 1) (hc : p.childField = true)
    (hr : p.childRC > 0) (hs : p.stampSlot = .fresh)
    (hp : p.freshPending = false) (hf : p.freshRC > 0) :
    (cStep p .decParent).map Physical.freshRC =
      some (p.freshRC - 1) := by
  have hn : p.freshRC ≠ 0 := Nat.ne_of_gt hf
  have hchild : p.childRC ≠ 0 := Nat.ne_of_gt hr
  simp [cStep, h, hc, hs, hp, hn, hchild]

def initial (oldExternal freshExternal : Nat) : Source :=
  { parentCredits := 1
    childField := true
    extraChild := 0
    oldExternal
    freshExternal
    stampSlot := .old
    freshPending := false
    childBorrowed := false }

def freshTrace : List Op :=
  [.borrowChild, .decOld, .incFresh, .storeFresh, .decParent]

def heldTrace : List Op :=
  [.borrowChild, .decOld, .incFresh, .storeFresh,
   .incChild, .decParent, .decLastChild]

def oldTrace : List Op := [.decParent]

def runSource : List Op → Source → Option Source
  | [], s => some s
  | op :: ops, s => do
      let next ← sourceStep s op
      runSource ops next

def runC : List Op → Physical → Option Physical
  | [], p => some p
  | x :: xs, p => do
      let after ← cStep p x
      runC xs after

/-- An old stamp has no field owner after last-parent release. -/
example :
    ((sourceStep (initial 1 1) .decParent).map
      (fun s => (represent s).oldRC)) = some 1 := by decide

/-- A fresh heap stamp similarly loses its field credit on final release. -/
example :
    ((runSource freshTrace (initial 1 1)).map
      (fun s => (represent s).freshRC)) = some 1 := by decide

/-- All admitted finite traces commute; the proof is by induction over steps,
not enumeration of a fixed set of examples. -/
theorem runC_represent (ops : List Op) (s : Source) :
    runC ops (represent s) = (runSource ops s).map represent := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      cases h : sourceStep s op with
      | none =>
          have hc : cStep (represent s) op = none := by
            simpa [h] using cStep_represent s op
          simp [runC, runSource, h, hc]
      | some next =>
          have hc : cStep (represent s) op = some (represent next) := by
            simpa [h] using cStep_represent s op
          simp [runC, runSource, h, hc, ih]

example :
    (runC freshTrace (represent (initial 1 1))).map Physical.freshRC =
      some 1 := by decide

example :
    (runC heldTrace (represent (initial 1 1))).map Physical.childRC =
      some 0 := by decide

example :
    (runC oldTrace (represent (initial 1 1))).map Physical.oldRC =
      some 1 := by decide

end ReaderCReleaseSemantics

#print axioms ReaderCReleaseSemantics.cStep_represent
#print axioms ReaderCReleaseSemantics.runC_represent
#print axioms ReaderCReleaseSemantics.store_fresh_does_not_increment
#print axioms ReaderCReleaseSemantics.shell_del_preserves_child_rc
#print axioms ReaderCReleaseSemantics.last_parent_release_drops_unretained_child
#print axioms ReaderCReleaseSemantics.last_parent_release_preserves_retained_child
#print axioms ReaderCReleaseSemantics.last_parent_release_fresh_stamp
