import Mathlib

/-!
# Universal exact count for normalized affine terminal systems

After an admitted row transcript, a terminal with r pivot rows and
f free internal bits has exactly one pivot completion for each free
assignment, whenever its boundary-only residual constraints hold.
This holds for every finite width and boundary assignment.

The terminal-shape model is not yet proved to be extracted from every
accepted raw checker snapshot. No Rust machine-code refinement is claimed.
-/

namespace IndependentETH.AffineTerminalSoundness

abbrev Bits (n : Nat) := Fin n → Bool

structure Terminal (r f b : Nat) where
  offset : Bits f → Bits b → Bits r
  target : Bits r
  residual : Bits b → Bool

def completePivots {r f b : Nat} (t : Terminal r f b)
    (free : Bits f) (boundary : Bits b) : Bits r :=
  fun i => t.target i ^^ t.offset free boundary i

def satisfies {r f b : Nat} (t : Terminal r f b)
    (pivot : Bits r) (free : Bits f) (boundary : Bits b) : Prop :=
  (∀ i, (pivot i ^^ t.offset free boundary i) = t.target i) ∧
    t.residual boundary = true

private theorem xor_rhs_iff (a correction rhs : Bool) :
    ((a ^^ correction) = rhs) ↔ (a = (rhs ^^ correction)) := by
  cases a <;> cases correction <;> cases rhs <;> decide

theorem satisfies_iff {r f b : Nat} (t : Terminal r f b)
    (pivot : Bits r) (free : Bits f) (boundary : Bits b) :
    satisfies t pivot free boundary ↔
      pivot = completePivots t free boundary ∧
      t.residual boundary = true := by
  constructor
  · rintro ⟨hpivot, hresidual⟩
    constructor
    · funext i
      exact (xor_rhs_iff
        (pivot i) (t.offset free boundary i) (t.target i)).mp (hpivot i)
    · exact hresidual
  · rintro ⟨hpivot, hresidual⟩
    constructor
    · intro i
      exact (xor_rhs_iff
        (pivot i) (t.offset free boundary i) (t.target i)).mpr
        (congrFun hpivot i)
    · exact hresidual

abbrev Solutions {r f b : Nat} (t : Terminal r f b)
    (boundary : Bits b) :=
  {x : Bits r × Bits f // satisfies t x.1 x.2 boundary}

noncomputable instance solutionsFintype {r f b : Nat}
    (t : Terminal r f b) (boundary : Bits b) :
    Fintype (Solutions t boundary) :=
  Fintype.ofFinite _

def solutionsEquivFree {r f b : Nat}
    (t : Terminal r f b) (boundary : Bits b)
    (h : t.residual boundary = true) :
    Solutions t boundary ≃ Bits f where
  toFun := fun x => x.val.2
  invFun := fun free =>
    ⟨(completePivots t free boundary, free),
      (satisfies_iff t (completePivots t free boundary) free boundary).mpr
        ⟨rfl, h⟩⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Prod.ext
    · exact (((satisfies_iff t x.val.1 x.val.2 boundary).mp x.property).1).symm
    · rfl
  right_inv := by
    intro free
    rfl

/-- The semantic count of any normalized terminal: exactly 2^f when
the boundary residual accepts, zero otherwise. No enumerated fixture. -/
theorem terminal_count {r f b : Nat}
    (t : Terminal r f b) (boundary : Bits b) :
    Fintype.card (Solutions t boundary) =
      if t.residual boundary then 2 ^ f else 0 := by
  classical
  cases hres : t.residual boundary with
  | false =>
      have hempty : IsEmpty (Solutions t boundary) :=
        ⟨fun x => by
          have h := x.property.2
          simp [hres] at h⟩
      letI := hempty
      simp [hres]
  | true =>
      have hc : Fintype.card (Bits f) = 2 ^ f := by
        simp [Bits]
      have hcard : Fintype.card (Solutions t boundary) = 2 ^ f :=
        (Fintype.card_congr (solutionsEquivFree t boundary hres)).trans hc
      simpa [hres] using hcard

theorem inconsistent_boundary_zero {r f b : Nat}
    (t : Terminal r f b) (boundary : Bits b)
    (h : t.residual boundary = false) :
    Fintype.card (Solutions t boundary) = 0 := by
  rw [terminal_count, h]
  rfl

#print axioms IndependentETH.AffineTerminalSoundness.satisfies_iff
#print axioms IndependentETH.AffineTerminalSoundness.solutionsEquivFree
#print axioms IndependentETH.AffineTerminalSoundness.terminal_count
#print axioms IndependentETH.AffineTerminalSoundness.inconsistent_boundary_zero

end IndependentETH.AffineTerminalSoundness
