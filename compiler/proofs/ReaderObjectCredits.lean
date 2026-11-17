import ReaderTransferCredits

/-!
# Allocation-indexed source reference transfers

A reference credit belongs to a specific allocation identity. Transferring
a credit between a caller and callee or a join formal never creates a credit
for another allocation. This strengthens the previous one-allocation ledger
to *arbitrarily many distinct allocation identities* and *arbitrarily long*
finite interleavings of direct-call and join transfers.

A Rust Rc alias count is a different field of each object's ledger; it
cannot lend a source reference to any allocation.

This is a mathematical source-accounting model, NOT a proof that the C
allocator, the Rust Rc adapter, or the pinned Lean.IR reader implements this
model on every possible heap.
-/

open ReaderTransferCredits

namespace ReaderObjectCredits

/-- Each Nat names a different source allocation. No global pooled credits. -/
abbrev Heap := Nat → Ledger

def put (h : Heap) (object : Nat) (ledger : Ledger) : Heap :=
  fun i => if i == object then ledger else h i

@[simp] theorem put_self (h : Heap) (i : Nat) (l : Ledger) :
    put h i l i = l := by simp [put]

@[simp] theorem put_other (h : Heap) (i j : Nat) (l : Ledger)
    (hij : j ≠ i) : put h i l j = h j := by
  simp [put, hij]

/-- A source operation acts on one explicit object identity. All other
object ledgers are bit-for-bit unchanged, not merely equal in total. -/
def stepAt (h : Heap) (object : Nat) (move : Move) : Option Heap := do
  let after ← step (h object) move
  some (put h object after)

def run : List (Nat × Move) → Heap → Option Heap
  | [], h => some h
  | (object, move) :: rest, h => do
      let after ← stepAt h object move
      run rest after

/-- Every admitted single transfer preserves every allocation's own
source reference count, independently of every other allocation. -/
theorem stepAt_conserves_each {h h' : Heap} {object : Nat} {move : Move}
    (ok : stepAt h object move = some h') (i : Nat) :
    sourceCount (h' i) = sourceCount (h i) := by
  unfold stepAt at ok
  cases hs : step (h object) move with
  | none => simp [hs] at ok
  | some v =>
      simp [hs] at ok
      subst h'
      by_cases hi : i = object
      · subst i
        simpa using (step_conserves hs)
      · simp [put, hi]

/-- Every finite, interleaved trace preserves the source count of *each*
allocation, not just the global total. This remains true if the sequence
contains many joins, calls and distinct object identities. -/
theorem every_successful_trace_conserves_each
    (moves : List (Nat × Move)) (h h' : Heap)
    (ok : run moves h = some h') (object : Nat) :
    sourceCount (h' object) = sourceCount (h object) := by
  induction moves generalizing h with
  | nil =>
      simp [run] at ok
      subst h'
      rfl
  | cons item rest ih =>
      rcases item with ⟨id, move⟩
      cases hs : stepAt h id move with
      | none => simp [run, hs] at ok
      | some mid =>
          have ht : run rest mid = some h' := by
            simpa [run, hs] using ok
          exact (ih mid ht).trans (stepAt_conserves_each hs object)

/-- A successful call or join on one object cannot touch even the
*ownership slots* of a different allocation. -/
theorem transfer_does_not_touch_other_object
    {h h' : Heap} {object : Nat} {move : Move}
    (ok : stepAt h object move = some h')
    (other : Nat) (distinct : other ≠ object) :
    h' other = h other := by
  unfold stepAt at ok
  cases hs : step (h object) move with
  | none => simp [hs] at ok
  | some v =>
      simp [hs] at ok
      subst h'
      simp [put, distinct]

/-- An explicit inc creates a credit for its target object only. -/
def incAt (h : Heap) (object : Nat) : Option Heap := do
  let after ← incCaller (h object)
  some (put h object after)

theorem incAt_target (h h' : Heap) (object : Nat)
    (ok : incAt h object = some h') :
    sourceCount (h' object) = sourceCount (h object) + 1 := by
  unfold incAt at ok
  cases hs : incCaller (h object) with
  | none => simp [hs] at ok
  | some v =>
      simp [hs] at ok
      subst h'
      simpa using (source_inc_increases_count hs)

theorem incAt_other (h h' : Heap) (object other : Nat)
    (ok : incAt h object = some h')
    (distinct : other ≠ object) :
    h' other = h other := by
  unfold incAt at ok
  cases hs : incCaller (h object) with
  | none => simp [hs] at ok
  | some v =>
      simp [hs] at ok
      subst h'
      simp [put, distinct]

def zero : Ledger := ⟨0, 0, 0, 0, 0⟩

/-- Two different live allocations; the first is only borrowed, the
second owns one caller source reference. Even an arbitrary Rc alias
count of the borrowed object never authorizes a direct owned transfer. -/
def twoObjects (firstAliases secondAliases : Nat) : Heap :=
  put (put (fun _ => zero) 0 (borrowedEntry firstAliases))
    1 ⟨1, 0, 0, 0, secondAliases⟩

theorem first_object_cannot_spend_second_object_credit
    (firstAliases secondAliases : Nat) :
    stepAt (twoObjects firstAliases secondAliases) 0 .callOwned = none := rfl

theorem second_object_can_transfer_its_own_credit
    (firstAliases secondAliases : Nat) :
    stepAt (twoObjects firstAliases secondAliases) 1 .callOwned =
      some (put (twoObjects firstAliases secondAliases) 1
        ⟨0, 1, 0, 0, secondAliases⟩) := rfl

/-- This is genuinely per-allocation. A global sum would not detect a
wrongly reassigned source credit between two allocations of equal count. -/
theorem crossing_object_identities_is_not_an_admitted_transfer
    (firstAliases secondAliases : Nat) :
    ∀ h',
      stepAt (twoObjects firstAliases secondAliases) 0 .callOwned ≠ some h' := by
  intro h' forbidden
  simpa [first_object_cannot_spend_second_object_credit] using forbidden

/-- A real trace may interleave a borrowed call on object 0 with an owned
call and return on object 1. The independent counts remain unchanged. -/
theorem interleaved_distinct_objects (firstAliases secondAliases : Nat) :
    ∃ after,
      run [(0, .callBorrowed), (1, .callOwned), (1, .returnOwnedCall)]
          (twoObjects firstAliases secondAliases) = some after ∧
      (∀ i, sourceCount (after i) =
        sourceCount ((twoObjects firstAliases secondAliases) i)) := by
  let initial := twoObjects firstAliases secondAliases
  let afterBorrow := put initial 0
      ⟨0, 0, 0, 1, firstAliases + 1⟩
  let afterOwnedCall := put afterBorrow 1
      ⟨0, 1, 0, 0, secondAliases⟩
  let after := put afterOwnedCall 1
      ⟨1, 0, 0, 0, secondAliases⟩
  have hr : run [(0, .callBorrowed), (1, .callOwned), (1, .returnOwnedCall)]
      initial = some after := by
    rfl
  exact ⟨after, hr,
    fun i => every_successful_trace_conserves_each _ initial after hr i⟩

end ReaderObjectCredits

#print axioms ReaderObjectCredits.stepAt_conserves_each
#print axioms ReaderObjectCredits.every_successful_trace_conserves_each
#print axioms ReaderObjectCredits.transfer_does_not_touch_other_object
#print axioms ReaderObjectCredits.incAt_target
#print axioms ReaderObjectCredits.incAt_other
#print axioms ReaderObjectCredits.first_object_cannot_spend_second_object_credit
#print axioms ReaderObjectCredits.second_object_can_transfer_its_own_credit
#print axioms ReaderObjectCredits.crossing_object_identities_is_not_an_admitted_transfer
#print axioms ReaderObjectCredits.interleaved_distinct_objects
