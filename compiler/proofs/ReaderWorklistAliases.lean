import Lean

/-!
# Aliased constructor-field releases: source-credit linearization

The pinned eager C++ lean_del_core walks *each* constructor field in
source order. Two fields can point to the same allocation. Its local dec
helper decrements a target with RC > 1 and queues it only when RC = 1.

The existing ReaderWorklistOrder.Tree proves visit-set preservation for
trees. It cannot express multiple incoming field edges to one identity.
This file models the missing *one-identity* ownership-credit boundary.

It is a mathematical model of single-threaded, positive, non-sticky RC
for ordinary constructor fields, NOT a refinement theorem for C++ memory,
atomic RC paths, object layout, allocator identity, or source translation.
The physical diagnostic independently checks the actual pinned C++ path.
-/

namespace ReaderWorklistAliases

/-- The owner count belongs to one concrete allocation identity.
`queued` marks the first (and only permitted) last-credit release.
A queued node has no readable source owner; there is no post-free access. -/
structure Credit where
  refs : Nat
  queued : Bool
  deriving Repr, DecidableEq

/-- One compiler-owned field spends exactly one credit. An ordinary
shared release reduces the RC; the final credit queues destruction.
No release is admitted after the last credit is scheduled. -/
def dropField (s : Credit) : Option Credit :=
  match s.refs, s.queued with
  | 0, _ => none
  | _, true => none
  | 1, false => some ⟨0, true⟩
  | n + 2, false => some ⟨n + 1, false⟩

/-- Apply `k` field releases to the *same* allocation identity. -/
def dropFields : Nat → Credit → Option Credit
  | 0, s => some s
  | n + 1, s => (dropField s).bind (dropFields n)

/-- Releasing k+1 source field credits from an allocation with
e independent owners yields exactly e outstanding credits.
If and only if e=0, the final field queues the allocation once.
This handles arbitrary finite alias multiplicity, not just a tree. -/
theorem alias_fields_spend_exactly_their_credits
    (external k : Nat) :
    dropFields (k + 1) ⟨external + k + 1, false⟩ =
      some ⟨external, external == 0⟩ := by
  induction k with
  | zero =>
      cases external with
      | zero =>
          decide
      | succ e =>
          simp [dropFields, dropField]
  | succ k ih =>
      have h : external + (k + 1) + 1 = (external + k) + 2 := by omega
      rw [h]
      change (dropField ⟨(external + k) + 2, false⟩).bind
        (dropFields (k + 1)) = some ⟨external, external == 0⟩
      have hdrop : dropField ⟨(external + k) + 2, false⟩ =
          some ⟨external + (k + 1), false⟩ := by
        simp [dropField, Nat.add_assoc]
      rw [hdrop]
      have heq : external + (k + 1) = external + k + 1 := by omega
      rw [heq]
      exact ih

/-- When an external owner survives, even arbitrarily many aliased
fields cannot enqueue its target. -/
theorem aliased_fields_preserve_external_owner (external k : Nat)
    (h : external > 0) :
    dropFields (k + 1) ⟨external + k + 1, false⟩ =
      some ⟨external, false⟩ := by
  rw [alias_fields_spend_exactly_their_credits]
  simp [Nat.ne_of_gt h]

/-- Without an external owner, the last of arbitrarily many incoming
field releases schedules one (not k+1) constructor destruction. -/
theorem alias_last_owner_enqueues_once (k : Nat) :
    dropFields (k + 1) ⟨k + 1, false⟩ =
      some ⟨0, true⟩ := by
  simpa using alias_fields_spend_exactly_their_credits 0 k

/-- A duplicated field consumes both credits and queues just once. -/
theorem duplicate_field_last_credit :
    dropFields 2 ⟨2, false⟩ = some ⟨0, true⟩ := by
  decide

/-- The retained diamond has two incoming constructor-field credits
but also one independent owner, so it does not queue. -/
theorem retained_diamond_stops :
    dropFields 2 ⟨3, false⟩ = some ⟨1, false⟩ := by
  decide

/-- Model-level fail-closedness. It is NOT evidence that the actual C++
runtime would safely reject a use-after-free pointer. -/
theorem spent_alias_cannot_release_again :
    dropField ⟨0, true⟩ = none := by rfl

/-- Independent physical state of the eager C++ constructor-field
`dec` path. The queued pointer still stores RC=1: scheduling the last
credit is not a physical decrement to zero. Its actual deallocation is
a separate worklist step, deliberately outside this one-identity model. -/
structure PhysicalCredit where
  rc : Nat
  pending : Bool
  deriving Repr, DecidableEq

/-- A single logical credit can be gone even though its queued, still-live
physical object has an RC field of one until its pending work is popped. -/
def represent (s : Credit) : PhysicalCredit :=
  ⟨if s.queued then 1 else s.refs, s.queued⟩

/-- An independently specified physical transition for pinned eager,
single-threaded, ordinary RC fields, not a call to `dropField`. -/
def physicalDrop (p : PhysicalCredit) : Option PhysicalCredit :=
  if p.pending then none
  else match p.rc with
    | 0 => none
    | 1 => some ⟨1, true⟩
    | n + 2 => some ⟨n + 1, false⟩

def physicalDrops : Nat → PhysicalCredit → Option PhysicalCredit
  | 0, p => some p
  | n + 1, p => (physicalDrop p).bind (physicalDrops n)

/-- Every modeled credit step, including refusals, is simulated by the
independent physical RC/pending transition after the representation map. -/
theorem physical_drop_simulates_source (s : Credit) :
    physicalDrop (represent s) = (dropField s).map represent := by
  rcases s with ⟨rc, queued⟩
  cases queued with
  | false =>
      cases rc with
      | zero => rfl
      | succ n =>
          cases n with
          | zero => rfl
          | succ k => rfl
  | true =>
      cases rc <;> rfl

/-- The step simulation lifts to arbitrary finite aliased-field traces.
This is a universal theorem of the two RESTRICTED machines, not a proof
that the compiled C++ code implements either transition semantics. -/
theorem physical_trace_simulates_source (n : Nat) (s : Credit) :
    physicalDrops n (represent s) = (dropFields n s).map represent := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change (physicalDrop (represent s)).bind (physicalDrops n) =
        ((dropField s).bind (dropFields n)).map represent
      rw [physical_drop_simulates_source]
      cases h : dropField s with
      | none => simp [h]
      | some next =>
          simpa [h] using ih next

/-- A queued last-credit release keeps physical RC=1 until worklist
processing. This rules out the tempting but false physical RC=0 model. -/
theorem queued_last_owner_has_physical_rc_one :
    represent ⟨0, true⟩ = ⟨1, true⟩ := by rfl

/-- Arbitrary finite incoming alias multiplicity has the expected
observable physical counter at the *enqueue* boundary. -/
theorem alias_physical_counter_at_queue_boundary (external k : Nat) :
    physicalDrops (k + 1) (represent ⟨external + k + 1, false⟩) =
      some ⟨if external == 0 then 1 else external, external == 0⟩ := by
  rw [physical_trace_simulates_source]
  rw [alias_fields_spend_exactly_their_credits]
  cases external with
  | zero => rfl
  | succ e => rfl

end ReaderWorklistAliases

#print axioms ReaderWorklistAliases.alias_fields_spend_exactly_their_credits
#print axioms ReaderWorklistAliases.aliased_fields_preserve_external_owner
#print axioms ReaderWorklistAliases.alias_last_owner_enqueues_once
#print axioms ReaderWorklistAliases.duplicate_field_last_credit
#print axioms ReaderWorklistAliases.retained_diamond_stops
#print axioms ReaderWorklistAliases.spent_alias_cannot_release_again

#print axioms ReaderWorklistAliases.physical_drop_simulates_source
#print axioms ReaderWorklistAliases.physical_trace_simulates_source
#print axioms ReaderWorklistAliases.queued_last_owner_has_physical_rc_one
#print axioms ReaderWorklistAliases.alias_physical_counter_at_queue_boundary
