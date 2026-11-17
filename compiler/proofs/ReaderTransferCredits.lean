import Lean

/-!
# Source reference credits across direct calls and join transfers

This is a finite, single-allocation source-accounting model. Its slots are
actual source-owned reference credits, not Rust Rc handles. An owned direct
call or join transfers one credit; a borrowed entry transfers none. Every
successful sequence of these ownership-preserving boundary operations keeps
the same total source count, independent of arbitrary Rc aliases.

It is NOT a physical Lean C/Rust heap simulation, an interprocedural
compiler correctness theorem, or a model of arbitrary closure capture.
Real Lean.IR.Param.borrow and FnBody.jmp acceptance checks live in the
separate production Reader fixtures.
-/

namespace ReaderTransferCredits

structure Ledger where
  caller : Nat
  callee : Nat
  join : Nat
  external : Nat
  rustAliases : Nat
  deriving Repr, DecidableEq

/-- The count represented by *source-owned* references to one allocation. -/
def sourceCount (s : Ledger) : Nat :=
  s.caller + s.callee + s.join + s.external

/-- An external owner protects a caller's borrowed formal. A Rust alias
is deliberately absent from this predicate. -/
def callerReadable (s : Ledger) : Bool :=
  (s.caller > 0) || (s.external > 0)

/-- An owned call moves one source credit from the caller to a callee formal.
The move itself cannot change the source object's physical RC. -/
def callOwned (s : Ledger) : Option Ledger :=
  if s.caller == 0 then none
  else some { s with caller := s.caller - 1, callee := s.callee + 1 }

/-- A borrowed callee can read a caller-protected object but receives no
source-owned reference. A compiler-internal Rust alias is not a credit. -/
def callBorrowed (s : Ledger) : Option Ledger :=
  if callerReadable s then
    some { s with rustAliases := s.rustAliases + 1 }
  else none

/-- An owned jump transfers an owned actual into the join's formal. -/
def jumpOwned (s : Ledger) : Option Ledger :=
  if s.caller == 0 then none
  else some { s with caller := s.caller - 1, join := s.join + 1 }

/-- A borrowed join parameter is protected by the same source owner as
its actual, but never acquires an independent source-owned credit. -/
def jumpBorrowed (s : Ledger) : Option Ledger :=
  if callerReadable s then
    some { s with rustAliases := s.rustAliases + 1 }
  else none

/-- Returning an owned call result transfers its credit back to the caller.
The returned handle can preserve the same allocation identity. -/
def returnOwnedCall (s : Ledger) : Option Ledger :=
  if s.callee == 0 then none
  else some { s with callee := s.callee - 1, caller := s.caller + 1 }

/-- Returning an owned join result transfers its credit to the enclosing
result. Here that destination is represented by the caller slot. -/
def returnOwnedJoin (s : Ledger) : Option Ledger :=
  if s.join == 0 then none
  else some { s with join := s.join - 1, caller := s.caller + 1 }

/-- Source IR .inc creates one *additional* owned credit, if the object
remains protected by an existing source owner. -/
def incCaller (s : Ledger) : Option Ledger :=
  if callerReadable s then some { s with caller := s.caller + 1 }
  else none

theorem callOwned_conserves {s t : Ledger}
    (h : callOwned s = some t) :
    sourceCount t = sourceCount s := by
  by_cases hz : s.caller = 0
  · simp [callOwned, hz] at h
  · have hpos : 0 < s.caller := Nat.pos_of_ne_zero hz
    simp [callOwned, hz] at h
    subst t
    simp only [sourceCount]
    omega

theorem callBorrowed_conserves {s t : Ledger}
    (h : callBorrowed s = some t) :
    sourceCount t = sourceCount s := by
  unfold callBorrowed at h
  split at h
  · cases h
    rfl
  · cases h

theorem jumpOwned_conserves {s t : Ledger}
    (h : jumpOwned s = some t) :
    sourceCount t = sourceCount s := by
  by_cases hz : s.caller = 0
  · simp [jumpOwned, hz] at h
  · have hpos : 0 < s.caller := Nat.pos_of_ne_zero hz
    simp [jumpOwned, hz] at h
    subst t
    simp only [sourceCount]
    omega

theorem jumpBorrowed_conserves {s t : Ledger}
    (h : jumpBorrowed s = some t) :
    sourceCount t = sourceCount s := by
  unfold jumpBorrowed at h
  split at h
  · cases h
    rfl
  · cases h

theorem returnOwnedCall_conserves {s t : Ledger}
    (h : returnOwnedCall s = some t) :
    sourceCount t = sourceCount s := by
  by_cases hz : s.callee = 0
  · simp [returnOwnedCall, hz] at h
  · have hpos : 0 < s.callee := Nat.pos_of_ne_zero hz
    simp [returnOwnedCall, hz] at h
    subst t
    simp only [sourceCount]
    omega

theorem returnOwnedJoin_conserves {s t : Ledger}
    (h : returnOwnedJoin s = some t) :
    sourceCount t = sourceCount s := by
  by_cases hz : s.join = 0
  · simp [returnOwnedJoin, hz] at h
  · have hpos : 0 < s.join := Nat.pos_of_ne_zero hz
    simp [returnOwnedJoin, hz] at h
    subst t
    simp only [sourceCount]
    omega

theorem source_inc_increases_count {s t : Ledger}
    (h : incCaller s = some t) :
    sourceCount t = sourceCount s + 1 := by
  unfold incCaller at h
  split at h
  · cases h
    simp [sourceCount]
    omega
  · cases h

/-- An arbitrary number of cloned Rust handles cannot create even one
Lean source-owned credit. -/
theorem rust_aliases_do_not_create_ownership (s : Ledger) (n : Nat) :
    sourceCount { s with rustAliases := n } = sourceCount s := rfl

/-- A finite mixed sequence of call/join transfers, including borrowed
entries and owned result forwarding, is source-count conserving. -/
inductive Move where
  | callOwned | callBorrowed | jumpOwned | jumpBorrowed
  | returnOwnedCall | returnOwnedJoin
  deriving Repr, DecidableEq

def step (s : Ledger) : Move → Option Ledger
  | .callOwned => callOwned s
  | .callBorrowed => callBorrowed s
  | .jumpOwned => jumpOwned s
  | .jumpBorrowed => jumpBorrowed s
  | .returnOwnedCall => returnOwnedCall s
  | .returnOwnedJoin => returnOwnedJoin s

def run : List Move → Ledger → Option Ledger
  | [], s => some s
  | m :: rest, s => do
      let after ← step s m
      run rest after

theorem step_conserves {s t : Ledger} {m : Move}
    (h : step s m = some t) :
    sourceCount t = sourceCount s := by
  cases m with
  | callOwned => exact callOwned_conserves h
  | callBorrowed => exact callBorrowed_conserves h
  | jumpOwned => exact jumpOwned_conserves h
  | jumpBorrowed => exact jumpBorrowed_conserves h
  | returnOwnedCall => exact returnOwnedCall_conserves h
  | returnOwnedJoin => exact returnOwnedJoin_conserves h

theorem every_successful_transfer_trace_conserves
    (moves : List Move) (s t : Ledger) (h : run moves s = some t) :
    sourceCount t = sourceCount s := by
  induction moves generalizing s with
  | nil =>
      simp [run] at h
      subst t
      rfl
  | cons m rest ih =>
      cases hs : step s m with
      | none =>
          simp [run, hs] at h
      | some mid =>
          have htail : run rest mid = some t := by
            simpa [run, hs] using h
          exact (ih mid htail).trans (step_conserves hs)

/-- The starting formal is borrowed, externally protected, and has no
transferable reference. Neither Rc aliases nor the external protector
authorize an *owned* call or jump without a preceding source inc. -/
def borrowedEntry (rustCopies : Nat) : Ledger :=
  ⟨0, 0, 0, 1, rustCopies⟩

theorem borrowed_without_inc_cannot_be_moved (rustCopies : Nat) :
    callOwned (borrowedEntry rustCopies) = none ∧
    jumpOwned (borrowedEntry rustCopies) = none := by
  constructor <;> rfl

theorem borrowed_can_forward_to_borrowed (rustCopies : Nat) :
    callBorrowed (borrowedEntry rustCopies) =
      some ⟨0, 0, 0, 1, rustCopies + 1⟩ ∧
    jumpBorrowed (borrowedEntry rustCopies) =
      some ⟨0, 0, 0, 1, rustCopies + 1⟩ := by
  constructor <;> rfl

/-- Explicit source inc permits exactly one owned parameter transfer;
the second owned argument cannot consume a fictitious credit. -/
theorem one_inc_authorizes_one_owned_transfer (rustCopies : Nat) :
    ∃ credited forwarded,
      incCaller (borrowedEntry rustCopies) = some credited ∧
      callOwned credited = some forwarded ∧
      callOwned forwarded = none ∧
      sourceCount forwarded = sourceCount (borrowedEntry rustCopies) + 1 := by
  exact ⟨⟨1, 0, 0, 1, rustCopies⟩,
    ⟨0, 1, 0, 1, rustCopies⟩, rfl, rfl, rfl, rfl⟩

/-- A callee returning the same owned allocation preserves its source
identity and exactly the pre-call source-reference count. -/
theorem owned_identity_return_conserves (rustCopies : Nat) :
    run [.callOwned, .returnOwnedCall]
      ⟨1, 0, 0, 0, rustCopies⟩ =
        some ⟨1, 0, 0, 0, rustCopies⟩ := rfl

theorem owned_join_return_conserves (rustCopies : Nat) :
    run [.jumpOwned, .returnOwnedJoin]
      ⟨1, 0, 0, 0, rustCopies⟩ =
        some ⟨1, 0, 0, 0, rustCopies⟩ := rfl

end ReaderTransferCredits

#print axioms ReaderTransferCredits.callOwned_conserves
#print axioms ReaderTransferCredits.callBorrowed_conserves
#print axioms ReaderTransferCredits.jumpOwned_conserves
#print axioms ReaderTransferCredits.jumpBorrowed_conserves
#print axioms ReaderTransferCredits.returnOwnedCall_conserves
#print axioms ReaderTransferCredits.returnOwnedJoin_conserves
#print axioms ReaderTransferCredits.source_inc_increases_count
#print axioms ReaderTransferCredits.rust_aliases_do_not_create_ownership
#print axioms ReaderTransferCredits.every_successful_transfer_trace_conserves
#print axioms ReaderTransferCredits.borrowed_without_inc_cannot_be_moved
#print axioms ReaderTransferCredits.borrowed_can_forward_to_borrowed
#print axioms ReaderTransferCredits.one_inc_authorizes_one_owned_transfer
#print axioms ReaderTransferCredits.owned_identity_return_conserves
#print axioms ReaderTransferCredits.owned_join_return_conserves
