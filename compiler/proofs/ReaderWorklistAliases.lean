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
          simp [dropFields, dropField, Nat.add_assoc]
  | succ k ih =>
      have h : external + (k + 1) + 1 = (external + k) + 2 := by omega
      rw [h]
      simp only [dropFields, dropField, Option.bind_some]
      simpa [Nat.add_assoc] using ih

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

end ReaderWorklistAliases

#print axioms ReaderWorklistAliases.alias_fields_spend_exactly_their_credits
#print axioms ReaderWorklistAliases.aliased_fields_preserve_external_owner
#print axioms ReaderWorklistAliases.alias_last_owner_enqueues_once
#print axioms ReaderWorklistAliases.duplicate_field_last_credit
#print axioms ReaderWorklistAliases.retained_diamond_stops
#print axioms ReaderWorklistAliases.spent_alias_cannot_release_again
