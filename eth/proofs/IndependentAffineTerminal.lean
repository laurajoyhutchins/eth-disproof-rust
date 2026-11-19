import Mathlib

/-!
# Exact counting from a terminal pivot/residual interface

This theorem formalizes the *terminal mathematical invariant* checked by
the Rust affine certificate verifier. Internal columns are separated
into pivot and free types; boundary values remain universally quantified.

The pivot equations have an identity coefficient on the pivot variables,
may depend on *all* free variables, and are accompanied by residual rows
depending only on boundary values. Every free assignment has exactly one
pivot extension when and only when the residual equations hold.

The split is invariant under an arbitrary equivalence of the actual
internal column index type with the disjoint sum of pivot/free indices.
This is *not* a proof of the executable Rust checker itself.
-/

namespace IndependentETH.AffineTerminal

abbrev GF2 := ZMod 2

structure Terminal (P F B R : Type) where
  freeCoeff : P → F → GF2
  pivotBoundaryCoeff : P → B → GF2
  pivotRhs : P → GF2
  residualBoundaryCoeff : R → B → GF2
  residualRhs : R → GF2

variable {P F B R : Type}
variable [Fintype P] [Fintype F] [Fintype B] [Fintype R]
variable [DecidableEq F] [DecidableEq B]

def freeTerm (t : Terminal P F B R) (i : P) (f : F → GF2) : GF2 :=
  ∑ j, t.freeCoeff i j * f j

def pivotBoundaryTerm (t : Terminal P F B R)
    (i : P) (b : B → GF2) : GF2 :=
  ∑ j, t.pivotBoundaryCoeff i j * b j

def residualBoundaryTerm (t : Terminal P F B R)
    (i : R) (b : B → GF2) : GF2 :=
  ∑ j, t.residualBoundaryCoeff i j * b j

def pivotEquation (t : Terminal P F B R)
    (p : P → GF2) (f : F → GF2) (b : B → GF2) (i : P) : Prop :=
  p i + freeTerm t i f + pivotBoundaryTerm t i b = t.pivotRhs i

def residualOK (t : Terminal P F B R) (b : B → GF2) : Prop :=
  ∀ i : R, residualBoundaryTerm t i b = t.residualRhs i

def satisfies (t : Terminal P F B R)
    (p : P → GF2) (f : F → GF2) (b : B → GF2) : Prop :=
  (∀ i, pivotEquation t p f b i) ∧ residualOK t b

/-- Unique pivot extension of an arbitrary free and external assignment. -/
def pivotSolution (t : Terminal P F B R)
    (f : F → GF2) (b : B → GF2) : P → GF2 :=
  fun i => t.pivotRhs i - freeTerm t i f - pivotBoundaryTerm t i b

theorem pivotEquation_iff (t : Terminal P F B R)
    (p : P → GF2) (f : F → GF2) (b : B → GF2) (i : P) :
    pivotEquation t p f b i ↔ p i = pivotSolution t f b i := by
  constructor
  · intro h
    dsimp [pivotEquation] at h
    dsimp [pivotSolution]
    calc
      p i = (p i + freeTerm t i f + pivotBoundaryTerm t i b) -
          freeTerm t i f - pivotBoundaryTerm t i b := by abel
      _ = t.pivotRhs i - freeTerm t i f - pivotBoundaryTerm t i b := by rw [h]
  · intro h
    dsimp [pivotEquation, pivotSolution] at *
    calc
      p i + freeTerm t i f + pivotBoundaryTerm t i b =
          (t.pivotRhs i - freeTerm t i f - pivotBoundaryTerm t i b) +
            freeTerm t i f + pivotBoundaryTerm t i b := by rw [h]
      _ = t.pivotRhs i := by abel

/-- A terminal matrix has exactly one pivot assignment per free
assignment if the residual boundary equations hold. -/
noncomputable def satisfyingEquivFree
    (t : Terminal P F B R) (b : B → GF2)
    (hres : residualOK t b) :
    {pf : (P → GF2) × (F → GF2) // satisfies t pf.1 pf.2 b} ≃ (F → GF2) where
  toFun := fun pf => pf.val.2
  invFun := fun f => ⟨(pivotSolution t f b, f), by
    constructor
    · intro i
      exact (pivotEquation_iff t (pivotSolution t f b) f b i).2 rfl
    · exact hres⟩
  left_inv := by
    intro pf
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hi := (pivotEquation_iff t pf.val.1 pf.val.2 b i).1 pf.property.1 i
      exact hi.symm
    · rfl
  right_inv := by
    intro f
    rfl

/-- Exact boundary count for *every* finite terminal pivot/residual
system, including free coefficients in the pivot rows. -/
theorem terminal_card (t : Terminal P F B R) (b : B → GF2) :
    Fintype.card
      {pf : (P → GF2) × (F → GF2) // satisfies t pf.1 pf.2 b} =
      if residualOK t b then 2 ^ Fintype.card F else 0 := by
  classical
  by_cases hres : residualOK t b
  · rw [if_pos hres]
    calc
      Fintype.card
          {pf : (P → GF2) × (F → GF2) // satisfies t pf.1 pf.2 b} =
          Fintype.card (F → GF2) :=
        Fintype.card_congr (satisfyingEquivFree t b hres)
      _ = 2 ^ Fintype.card F := by
        simp [GF2, Fintype.card_fun]
  · rw [if_neg hres]
    have hempty :
        IsEmpty {pf : (P → GF2) × (F → GF2) //
          satisfies t pf.1 pf.2 b} := ⟨by
      intro pf
      exact hres pf.property.2⟩
    letI := hempty
    simp

/-!
An arbitrary ordering of the *actual* internal columns is immaterial.
A supplied bijection from columns to pivot/free indices represents the
partition validated by the independent terminal checker.
-/

variable {I : Type} [Fintype I]

noncomputable def columnSplit (e : I ≃ Sum P F) :
    (I → GF2) ≃ ((P → GF2) × (F → GF2)) where
  toFun := fun u =>
    (fun p => u (e.symm (Sum.inl p)), fun f => u (e.symm (Sum.inr f)))
  invFun := fun pf i =>
    match e i with
    | .inl p => pf.1 p
    | .inr f => pf.2 f
  left_inv := by
    intro u
    funext i
    cases h : e i with
    | inl p =>
        have hs : e.symm (Sum.inl p) = i := by
          rw [← h]
          exact e.symm_apply_apply i
        simp [h, hs]
    | inr f =>
        have hs : e.symm (Sum.inr f) = i := by
          rw [← h]
          exact e.symm_apply_apply i
        simp [h, hs]
  right_inv := by
    intro pf
    apply Prod.ext
    · funext p
      simp
    · funext f
      simp

def satisfiesColumns (t : Terminal P F B R)
    (e : I ≃ Sum P F) (u : I → GF2) (b : B → GF2) : Prop :=
  satisfies t (columnSplit e u).1 (columnSplit e u).2 b

noncomputable def columnSolutionEquiv
    (t : Terminal P F B R) (e : I ≃ Sum P F) (b : B → GF2) :
    {u : I → GF2 // satisfiesColumns t e u b} ≃
      {pf : (P → GF2) × (F → GF2) // satisfies t pf.1 pf.2 b} where
  toFun := fun u => ⟨columnSplit e u.val, u.property⟩
  invFun := fun pf => ⟨(columnSplit e).symm pf.val, by
    simpa [satisfiesColumns] using pf.property⟩
  left_inv := by
    intro u
    apply Subtype.ext
    simp
  right_inv := by
    intro pf
    apply Subtype.ext
    simp

/-- The same exact count holds under any bijective reindexing of
internal columns, so pivot variables need not be a contiguous prefix. -/
theorem terminal_card_arbitrary_columns
    (t : Terminal P F B R) (e : I ≃ Sum P F) (b : B → GF2) :
    Fintype.card {u : I → GF2 // satisfiesColumns t e u b} =
      if residualOK t b then 2 ^ Fintype.card F else 0 := by
  classical
  calc
    Fintype.card {u : I → GF2 // satisfiesColumns t e u b} =
      Fintype.card
        {pf : (P → GF2) × (F → GF2) // satisfies t pf.1 pf.2 b} :=
      Fintype.card_congr (columnSolutionEquiv t e b)
    _ = if residualOK t b then 2 ^ Fintype.card F else 0 := terminal_card t b

#print axioms IndependentETH.AffineTerminal.pivotEquation_iff
#print axioms IndependentETH.AffineTerminal.satisfyingEquivFree
#print axioms IndependentETH.AffineTerminal.terminal_card
#print axioms IndependentETH.AffineTerminal.terminal_card_arbitrary_columns
