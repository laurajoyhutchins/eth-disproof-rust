import Mathlib
import ACC.ArrayStepSimulation

/-!
# Full vertex-major array-scan simulation

The previous proof relates one successful indexed-array update to one
mathematical function-state update. Here the concrete-shaped scan recurses
over the entire ordered vertex stream, without assuming the final array was
already grouped correctly. Induction composes the single-step relation.

Success is a partial refinement: these theorems do not assert that an
out-of-range input must succeed or that the mutable Rust implementation
has been translated to Lean. The Rust scan is tested independently.
-/

namespace ACC.ArrayScanSimulation

open ACC.ArrayStepSimulation
open ACC.ComponentFoldCorrespondence

/-- Concrete array loop over vertices, in precisely their input order.
    Failed indexed lookup or checked arithmetic stops this scan. -/
def checkedArrayScanFrom {c : ℕ}
    (array : Array (ℤ × ℤ)) :
    List (Fin c × (ℤ × ℤ)) → Option (Array (ℤ × ℤ))
  | [] => some array
  | item :: rest =>
      (checkedArrayStep array item).bind
        (fun next => checkedArrayScanFrom next rest)

/-- Composing the proved one-step simulation across an arbitrarily long
    finite stream preserves the entire array-to-function relation.
    No intermediate state is assumed to be correct without induction. -/
theorem checkedArrayScanFrom_refines {c : ℕ}
    (array result : Array (ℤ × ℤ))
    (state : Products c)
    (items : List (Fin c × (ℤ × ℤ)))
    (hrep : Represents array state)
    (hrun : checkedArrayScanFrom array items = some result) :
    ∃ finalState : Products c,
      checkedScanFrom state items = some finalState ∧
      Represents result finalState := by
  induction items generalizing array state with
  | nil =>
      have heq : array = result := by
        exact Option.some.inj (by simpa [checkedArrayScanFrom] using hrun)
      subst result
      exact ⟨state, rfl, hrep⟩
  | cons item rest ih =>
      cases hs : checkedArrayStep array item with
      | none =>
          simp [checkedArrayScanFrom, hs] at hrun
      | some next =>
          have htail : checkedArrayScanFrom next rest = some result := by
            simpa [checkedArrayScanFrom, hs] using hrun
          obtain ⟨nextState, hstep, hnext⟩ :=
            checkedArrayStep_refines array next state item hrep hs
          obtain ⟨finalState, hrest, hfinal⟩ :=
            ih next nextState hnext htail
          refine ⟨finalState, ?_, hfinal⟩
          simpa [checkedScanFrom, hstep] using hrest

/-- The abstract state returned by a successful concrete-shaped scan
    also agrees with the unconditional unbounded mathematical scan. -/
theorem checkedArrayScanFrom_unbounded {c : ℕ}
    (array result : Array (ℤ × ℤ))
    (state : Products c)
    (items : List (Fin c × (ℤ × ℤ)))
    (hrep : Represents array state)
    (hrun : checkedArrayScanFrom array items = some result) :
    ∃ finalState : Products c,
      Represents result finalState ∧
      finalState = uncheckedScanFrom state items := by
  obtain ⟨finalState, hchecked, hfinal⟩ :=
    checkedArrayScanFrom_refines array result state items hrep hrun
  refine ⟨finalState, hfinal, ?_⟩
  exact checkedScanFrom_sound state items finalState hchecked

/-- Full-scan array invariant: every concrete component slot represents
    precisely the factors in that class's fiber, in input order. -/
theorem checkedArrayScanFrom_fiber {c : ℕ}
    (array result : Array (ℤ × ℤ))
    (state : Products c)
    (items : List (Fin c × (ℤ × ℤ)))
    (hrep : Represents array state)
    (hrun : checkedArrayScanFrom array items = some result) :
    ∃ finalState : Products c,
      Represents result finalState ∧
      ∀ (k : Fin c) (bit : Bool),
        choose (finalState k) bit =
          choose (state k) bit * fiberProduct items k bit := by
  obtain ⟨finalState, hfinal, heq⟩ :=
    checkedArrayScanFrom_unbounded array result state items hrep hrun
  refine ⟨finalState, hfinal, ?_⟩
  intro k bit
  rw [heq]
  exact uncheckedScanFrom_fiber state items k bit

/-- Rust-style initialization by allocating one [1,1] pair per class
    represents the mathematical constant-one accumulator, even for c=0. -/
theorem replicate_represents (c : ℕ) :
    Represents (Array.replicate c (1, 1)) (initialProducts c) := by
  constructor
  · simp
  · intro k
    simp [initialProducts, Array.getElem?_replicate, k.isLt]

/-- Specialization to a scan starting from the actual initialized array. -/
theorem checkedArrayScan_initial_refines {c : ℕ}
    (items : List (Fin c × (ℤ × ℤ)))
    (result : Array (ℤ × ℤ))
    (h : checkedArrayScanFrom
      (Array.replicate c (1, 1)) items = some result) :
    ∃ finalState : Products c,
      checkedScanFrom (initialProducts c) items = some finalState ∧
      Represents result finalState := by
  exact checkedArrayScanFrom_refines
    (Array.replicate c (1, 1)) result
    (initialProducts c) items (replicate_represents c) h

/-- An empty array scan returns the same array and does not invent any
    phantom component or source vertex. -/
example :
    checkedArrayScanFrom (#[] : Array (ℤ × ℤ))
      ([] : List (Fin 0 × (ℤ × ℤ))) = some #[] := by rfl

#print axioms ACC.ArrayScanSimulation.checkedArrayScanFrom_refines
#print axioms ACC.ArrayScanSimulation.checkedArrayScanFrom_unbounded
#print axioms ACC.ArrayScanSimulation.checkedArrayScanFrom_fiber
#print axioms ACC.ArrayScanSimulation.replicate_represents
#print axioms ACC.ArrayScanSimulation.checkedArrayScan_initial_refines

end ACC.ArrayScanSimulation
