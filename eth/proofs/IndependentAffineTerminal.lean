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

attribute [local instance] Classical.propDecidable

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
      have hi := (pivotEquation_iff t pf.val.1 pf.val.2 b i).1 (pf.property.1 i)
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



/-!
## Checked replayed rows: exact-count soundness of the terminal *decision*

This faithfully models the independent Rust checker's final structural
conditions, after the source rows have been replayed and their columns
partitioned into pivot, free and boundary coordinates.

The checker does not assume that free coefficients in pivot rows vanish.
It checks that the pivot-pivot submatrix is the identity and both
residual-internal blocks vanish. The resulting acceptance decision
implies exact counting of the *original full row equations*.

This is a theorem about a pure checker specification, not yet
verification of the Rust implementation of that specification.
-/

structure ReplayedRows (P F B R : Type) where
  pivotPivot : P → P → GF2
  pivotFree : P → F → GF2
  pivotBoundary : P → B → GF2
  pivotRhs : P → GF2
  residualPivot : R → P → GF2
  residualFree : R → F → GF2
  residualBoundary : R → B → GF2
  residualRhs : R → GF2

/-- Precisely the coefficient-shape conditions checked by the native
terminal verifier, after a validated pivot/free and row partition. -/
def TerminalShape [DecidableEq P]
    (rows : ReplayedRows P F B R) : Prop :=
  (∀ i j : P, rows.pivotPivot i j =
    if i = j then 1 else 0) ∧
  (∀ q : R, ∀ i : P, rows.residualPivot q i = 0) ∧
  (∀ q : R, ∀ j : F, rows.residualFree q j = 0)

/-- Boolean acceptance decision on the replayed matrix blocks. -/
noncomputable def checkTerminalRows [DecidableEq P]
    (rows : ReplayedRows P F B R) : Bool :=
  decide (TerminalShape rows)

theorem checkTerminalRows_iff [DecidableEq P]
    (rows : ReplayedRows P F B R) :
    checkTerminalRows rows = true ↔ TerminalShape rows := by
  simp [checkTerminalRows]

/-- Unlike a reduced interface, these equations retain *all* internal
coefficients and therefore describe the raw terminal matrix directly. -/
def satisfiesFullRows (rows : ReplayedRows P F B R)
    (p : P → GF2) (f : F → GF2) (b : B → GF2) : Prop :=
  (∀ i : P,
    (∑ j : P, rows.pivotPivot i j * p j) +
      (∑ j : F, rows.pivotFree i j * f j) +
      (∑ j : B, rows.pivotBoundary i j * b j) = rows.pivotRhs i) ∧
  (∀ q : R,
    (∑ i : P, rows.residualPivot q i * p i) +
      (∑ j : F, rows.residualFree q j * f j) +
      (∑ j : B, rows.residualBoundary q j * b j) = rows.residualRhs q)

/-- Extract the exact terminal interface from the accepted raw matrix,
not from the producer's claimed interface. -/
def asTerminal (rows : ReplayedRows P F B R) : Terminal P F B R where
  freeCoeff := rows.pivotFree
  pivotBoundaryCoeff := rows.pivotBoundary
  pivotRhs := rows.pivotRhs
  residualBoundaryCoeff := rows.residualBoundary
  residualRhs := rows.residualRhs

theorem pivotBlock_sum_eq [DecidableEq P]
    (rows : ReplayedRows P F B R)
    (h : TerminalShape rows) (p : P → GF2) (i : P) :
    (∑ j : P, rows.pivotPivot i j * p j) = p i := by
  calc
    (∑ j : P, rows.pivotPivot i j * p j) =
        (∑ j : P, (if i = j then (1 : GF2) else 0) * p j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [h.1 i j]
    _ = p i := by simp

theorem residualBlock_sum_zero [DecidableEq P]
    (rows : ReplayedRows P F B R)
    (h : TerminalShape rows) (p : P → GF2) (f : F → GF2) (q : R) :
    (∑ i : P, rows.residualPivot q i * p i) = 0 ∧
    (∑ j : F, rows.residualFree q j * f j) = 0 := by
  constructor
  · apply Finset.sum_eq_zero
    intro i _
    rw [h.2.1 q i]
    simp
  · apply Finset.sum_eq_zero
    intro j _
    rw [h.2.2 q j]
    simp

theorem fullRows_iff_terminal [DecidableEq P]
    (rows : ReplayedRows P F B R) (h : TerminalShape rows)
    (p : P → GF2) (f : F → GF2) (b : B → GF2) :
    satisfiesFullRows rows p f b ↔ satisfies (asTerminal rows) p f b := by
  have hp (i : P) :
      (∑ j : P, rows.pivotPivot i j * p j) +
      (∑ j : F, rows.pivotFree i j * f j) +
      (∑ j : B, rows.pivotBoundary i j * b j) =
      p i + freeTerm (asTerminal rows) i f +
        pivotBoundaryTerm (asTerminal rows) i b := by
    rw [pivotBlock_sum_eq rows h p i]
    rfl
  have hr (q : R) :
      (∑ i : P, rows.residualPivot q i * p i) +
      (∑ j : F, rows.residualFree q j * f j) +
      (∑ j : B, rows.residualBoundary q j * b j) =
      residualBoundaryTerm (asTerminal rows) q b := by
    obtain ⟨hzeroP, hzeroF⟩ := residualBlock_sum_zero rows h p f q
    rw [hzeroP, hzeroF]
    simp [residualBoundaryTerm, asTerminal]
  constructor
  · intro hs
    constructor
    · intro i
      have hi := hs.1 i
      rw [hp i] at hi
      exact hi
    · intro q
      have hq := hs.2 q
      rw [hr q] at hq
      exact hq
  · intro hs
    constructor
    · intro i
      rw [hp i]
      exact hs.1 i
    · intro q
      rw [hr q]
      exact hs.2 q

/-- The main missing mathematical connection: acceptance of the
*actual full terminal matrix* implies the exact number of internal
assignments, for every boundary, without trusting claimed rank,
multiplicity or residual rows. -/
theorem checked_terminal_count [DecidableEq P]
    (rows : ReplayedRows P F B R)
    (h : checkTerminalRows rows = true)
    (b : B → GF2) :
    Fintype.card
      {pf : (P → GF2) × (F → GF2) //
        satisfiesFullRows rows pf.1 pf.2 b} =
      if residualOK (asTerminal rows) b
      then 2 ^ Fintype.card F else 0 := by
  classical
  have hs : TerminalShape rows := (checkTerminalRows_iff rows).mp h
  let e :
      {pf : (P → GF2) × (F → GF2) //
        satisfiesFullRows rows pf.1 pf.2 b} ≃
      {pf : (P → GF2) × (F → GF2) //
        satisfies (asTerminal rows) pf.1 pf.2 b} :=
    { toFun := fun pf =>
        ⟨pf.val, (fullRows_iff_terminal rows hs pf.val.1 pf.val.2 b).mp pf.property⟩
      invFun := fun pf =>
        ⟨pf.val, (fullRows_iff_terminal rows hs pf.val.1 pf.val.2 b).mpr pf.property⟩
      left_inv := fun pf => Subtype.ext rfl
      right_inv := fun pf => Subtype.ext rfl }
  exact (Fintype.card_congr e).trans (terminal_card (asTerminal rows) b)

#print axioms IndependentETH.AffineTerminal.checkTerminalRows_iff
#print axioms IndependentETH.AffineTerminal.pivotBlock_sum_eq
#print axioms IndependentETH.AffineTerminal.residualBlock_sum_zero
#print axioms IndependentETH.AffineTerminal.fullRows_iff_terminal
#print axioms IndependentETH.AffineTerminal.checked_terminal_count

#print axioms IndependentETH.AffineTerminal.pivotEquation_iff
#print axioms IndependentETH.AffineTerminal.satisfyingEquivFree
#print axioms IndependentETH.AffineTerminal.terminal_card
#print axioms IndependentETH.AffineTerminal.terminal_card_arbitrary_columns
