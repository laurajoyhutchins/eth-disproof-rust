import Mathlib
import ACC.ComponentFoldCorrespondence

/-!
# One-step simulation of the mutable component-product array

The mathematical state is a function Fin c → ℤ × ℤ. The executable-shaped
state is an Array (ℤ × ℤ) with an explicit length invariant. Every slot is
related to its mathematical counterpart by a checked optional lookup; no
default, out-of-bounds value is silently accepted.

The reference array update reads one component slot, computes both checked
integer multiplications, and writes the pair only after both succeed. A
successful array transition simulates the previous function-valued
checkedStep. This proof is not about compiled Rust machine code.
-/

namespace ACC.ArrayStepSimulation

open ACC.ComponentFoldCorrespondence
open ACC.CheckedComponentArithmetic

/-- Concrete-array to abstract-state simulation relation. The width
    requirement is essential, including the zero-class case. -/
def Represents {c : ℕ}
    (array : Array (ℤ × ℤ)) (state : Products c) : Prop :=
  array.size = c ∧
    ∀ k : Fin c, array[k.val]? = some (state k)

/-- Array-shaped update, using an optional bounds-checked source lookup.
    Both products must succeed before the array is changed. -/
def checkedArrayStep {c : ℕ}
    (array : Array (ℤ × ℤ)) (item : Fin c × (ℤ × ℤ)) :
    Option (Array (ℤ × ℤ)) := do
  let old ← array[item.1.val]?
  let zero ← checkedMul old.1 item.2.1
  let one ← checkedMul old.2 item.2.2
  some (array.set item.1.val (zero, one))

/-- A single successful array update simulates the mathematical checked
    update, with all unaffected slots preserved. This is a theorem about
    the Lean array interpreter and its explicit relation, not Rust machine code. -/
theorem checkedArrayStep_refines {c : ℕ}
    (array next : Array (ℤ × ℤ))
    (state : Products c) (item : Fin c × (ℤ × ℤ))
    (hrep : Represents array state)
    (hstep : checkedArrayStep array item = some next) :
    ∃ nextState : Products c,
      checkedStep state item = some nextState ∧
      Represents next nextState := by
  rcases hrep with ⟨hsize, hslots⟩
  have hin : item.1.val < array.size := by
    rw [hsize]
    exact item.1.isLt
  have hread := hslots item.1
  have hrun :
      (do
        let zero ← checkedMul (state item.1).1 item.2.1
        let one ← checkedMul (state item.1).2 item.2.2
        some (array.set item.1.val (zero, one))) = some next := by
    simpa [checkedArrayStep, hread] using hstep
  cases hz : checkedMul (state item.1).1 item.2.1 with
  | none =>
      simp [hz] at hrun
  | some zero =>
      cases ho : checkedMul (state item.1).2 item.2.2 with
      | none =>
          simp [hz, ho] at hrun
      | some one =>
          have harray : array.set item.1.val (zero, one) = next := by
            simpa [hz, ho] using hrun
          let nextState : Products c :=
            fun k => if item.1 = k then (zero, one) else state k
          refine ⟨nextState, ?_, ?_⟩
          · simp [checkedStep, hz, ho, nextState]
          · rw [← harray]
            constructor
            · simpa using hsize
            · intro k
              by_cases hk : item.1 = k
              · subst k
                simpa [nextState] using
                  (Array.getElem?_set_self (xs := array)
                    (i := item.1.val) (v := (zero, one)) hin)
              · have hne : item.1.val ≠ k.val := by
                  intro h
                  apply hk
                  exact Fin.ext h
                rw [Array.getElem?_set_ne hin hne]
                simpa [nextState, hk] using hslots k

/-- A checked array update cannot succeed for a truly absent source slot. -/
theorem checkedArrayStep_refuses_absent {c : ℕ}
    (array : Array (ℤ × ℤ)) (item : Fin c × (ℤ × ℤ))
    (h : array[item.1.val]? = none) :
    checkedArrayStep array item = none := by
  simp [checkedArrayStep, h]

/-- The empty array represents the empty mathematical state. -/
example : Represents (#[] : Array (ℤ × ℤ))
    (fun k : Fin 0 => k.elim0) := by
  constructor
  · rfl
  · intro k
    exact k.elim0

#print axioms ACC.ArrayStepSimulation.checkedArrayStep_refines
#print axioms ACC.ArrayStepSimulation.checkedArrayStep_refuses_absent

end ACC.ArrayStepSimulation
