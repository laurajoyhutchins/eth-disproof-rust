import Mathlib

/-!
# Quadratic Boolean boundary modes: first exact algebraic interface

Values live in the integers although the phase is Boolean. Affine and
quadratic phases have explicit bounded-degree coefficient syntax.
The exact projection and stitching rules hold for every exterior setting.

This is not yet a source-specific proof of Anthropic's eight-square
factorization or OpenAI's truncated moment recursion. A computable
canonical RREF and full bit-cost refinement remain separate obligations.
-/

namespace IndependentETH.QuadraticBoundary

open scoped BigOperators

/-- A sign evaluated as an exact integer, never modulo two. -/
def sign (bit : Bool) : ℤ := if bit = true then -1 else 1

theorem sign_xor (a b : Bool) : sign (a ^^ b) = sign a * sign b := by
  cases a <;> cases b <;> decide

/-- Summing a linear character over one internal Boolean variable. -/
theorem sum_sign_xor (a ell : Bool) :
    (∑ x : Bool, sign (a ^^ (x && ell))) =
      if ell = true then 0 else 2 * sign a := by
  cases a <;> cases ell <;> decide

/-- An affine ANF with explicitly bounded polynomial degree. -/
structure Affine (n : ℕ) where
  constant : Bool
  linear : Fin n → Bool

/-- A quadratic ANF. Diagonal terms are allowed as redundant input syntax. -/
structure Quadratic (n : ℕ) where
  constant : Bool
  linear : Fin n → Bool
  quadratic : Fin n → Fin n → Bool

/-- XOR parity of finitely many Boolean indicators. -/
def xorParity {α : Type*} [Fintype α] [DecidableEq α] (f : α → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => f i = true)).card % 2 = 1)

def Affine.eval {n : ℕ} (a : Affine n) (b : Fin n → Bool) : Bool :=
  a.constant ^^ xorParity (fun i => a.linear i && b i)

def Quadratic.eval {n : ℕ} (q : Quadratic n) (b : Fin n → Bool) : Bool :=
  q.constant ^^ xorParity (fun i => q.linear i && b i) ^^
    xorParity (fun ij : Fin n × Fin n => q.quadratic ij.1 ij.2 && b ij.1 && b ij.2)

/-- The internal variable x occurs with an affine coefficient, while the
boundary-only phase is quadratic. -/
structure SplitPhase (n : ℕ) where
  base : Quadratic n
  mixed : Affine n

def SplitPhase.eval {n : ℕ} (p : SplitPhase n) (x : Bool)
    (b : Fin n → Bool) : Bool :=
  p.base.eval b ^^ (x && p.mixed.eval b)

/-- The exact value of free-variable elimination for every boundary value. -/
theorem project_free_exact {n : ℕ} (p : SplitPhase n) (b : Fin n → Bool) :
    (∑ x : Bool, sign (p.eval x b)) =
      if p.mixed.eval b = true then 0 else 2 * sign (p.base.eval b) := by
  exact sum_sign_xor (p.base.eval b) (p.mixed.eval b)

/-- Common integer powers of two and boundary feasibility may be retained
through the projection, with a new affine support condition. -/
theorem project_free_weighted_exact {n : ℕ} (p : SplitPhase n)
    (feasible : (Fin n → Bool) → Bool) (k : ℕ) (b : Fin n → Bool) :
    (∑ x : Bool, if feasible b = true then
        (2 : ℤ) ^ k * sign (p.eval x b) else 0) =
      (if (feasible b && !(p.mixed.eval b)) = true then
        (2 : ℤ) ^ (k + 1) * sign (p.base.eval b) else 0) := by
  cases hf : feasible b <;> cases hl : p.mixed.eval b <;>
    cases hq : p.base.eval b <;>
    simp [SplitPhase.eval, sign, hl, hq, pow_succ] <;> ring


/-- An affine monomial is either the constant or one boundary variable. -/
abbrev AffineTerm (n : ℕ) := Option (Fin n)

def evalAffineTerm {n : ℕ} (b : Fin n → Bool) : AffineTerm n → Bool
  | none => true
  | some i => b i

/-- Sparse squarefree terms. Repeated terms in a list encode coefficient XOR. -/
inductive SquarefreeTerm (n : ℕ)
  | constant
  | linear (i : Fin n)
  | pair (i j : Fin n)

def evalSquarefreeTerm {n : ℕ} (b : Fin n → Bool) : SquarefreeTerm n → Bool
  | .constant => true
  | .linear i => b i
  | .pair i j => b i && b j

def affineAsSquarefree {n : ℕ} : AffineTerm n → SquarefreeTerm n
  | none => .constant
  | some i => .linear i

def multiplyAffineTerms {n : ℕ} : AffineTerm n → AffineTerm n → SquarefreeTerm n
  | none, t => affineAsSquarefree t
  | t, none => affineAsSquarefree t
  | some i, some j =>
      if i = j then .linear i else if i < j then .pair i j else .pair j i

theorem eval_multiplyAffineTerms {n : ℕ} (b : Fin n → Bool)
    (s t : AffineTerm n) :
    evalSquarefreeTerm b (multiplyAffineTerms s t) =
      (evalAffineTerm b s && evalAffineTerm b t) := by
  cases s with
  | none => cases t <;> simp [multiplyAffineTerms, affineAsSquarefree,
      evalSquarefreeTerm, evalAffineTerm]
  | some i =>
      cases t with
      | none => simp [multiplyAffineTerms, affineAsSquarefree, evalSquarefreeTerm,
          evalAffineTerm]
      | some j =>
          by_cases h : i = j
          · subst j
            simp [multiplyAffineTerms, evalSquarefreeTerm, evalAffineTerm]
          · by_cases hlt : i < j <;>
              simp [multiplyAffineTerms, evalSquarefreeTerm, evalAffineTerm,
                h, hlt, Bool.and_comm]

def termParity {α : Type*} (eval : α → Bool) : List α → Bool
  | [] => false
  | a :: as => eval a ^^ termParity eval as

theorem termParity_append {α : Type*} (eval : α → Bool) (xs ys : List α) :
    termParity eval (xs ++ ys) = (termParity eval xs ^^ termParity eval ys) := by
  induction xs with
  | nil => simp [termParity]
  | cons a as ih =>
      simp only [List.cons_append, termParity, ih]
      cases eval a <;> cases termParity eval as <;> cases termParity eval ys <;> decide

private theorem eval_affine_row_product {n : ℕ} (b : Fin n → Bool)
    (s : AffineTerm n) (ts : List (AffineTerm n)) :
    termParity (evalSquarefreeTerm b) (ts.map (multiplyAffineTerms s)) =
      (evalAffineTerm b s && termParity (evalAffineTerm b) ts) := by
  induction ts with
  | nil => simp [termParity]
  | cons t ts ih =>
      simp only [List.map_cons, termParity, eval_multiplyAffineTerms, ih]
      cases evalAffineTerm b s <;> cases evalAffineTerm b t <;>
        cases termParity (evalAffineTerm b) ts <;> decide

def affineProduct {n : ℕ} (ts : List (AffineTerm n)) :
    List (AffineTerm n) → List (SquarefreeTerm n)
  | [] => []
  | s :: ss => ts.map (multiplyAffineTerms s) ++ affineProduct ts ss

theorem eval_affineProduct {n : ℕ} (b : Fin n → Bool)
    (ss ts : List (AffineTerm n)) :
    termParity (evalSquarefreeTerm b) (affineProduct ts ss) =
      (termParity (evalAffineTerm b) ss && termParity (evalAffineTerm b) ts) := by
  induction ss with
  | nil => simp [affineProduct, termParity]
  | cons s ss ih =>
      simp only [affineProduct, termParity_append, eval_affine_row_product,
        termParity, ih]
      cases evalAffineTerm b s <;> cases termParity (evalAffineTerm b) ss <;>
        cases termParity (evalAffineTerm b) ts <;> decide

/-- A row stores the coefficient of the eliminated variable separately. -/
structure SplitRow (n : ℕ) where
  coefficient : Bool
  boundary : List (AffineTerm n)
  rhs : Bool

def SplitRow.holds {n : ℕ} (row : SplitRow n) (x : Bool) (b : Fin n → Bool) : Bool :=
  (termParity (evalAffineTerm b) row.boundary ^^ (row.coefficient && x)) == row.rhs

def SplitRow.residual {n : ℕ} (row : SplitRow n) (pivot : List (AffineTerm n)) :
    List (AffineTerm n) :=
  row.boundary ++ if row.coefficient then pivot else []

theorem SplitRow.residual_holds {n : ℕ} (row : SplitRow n)
    (pivot : List (AffineTerm n)) (b : Fin n → Bool) :
    (termParity (evalAffineTerm b) (row.residual pivot) == row.rhs) =
      row.holds (termParity (evalAffineTerm b) pivot) b := by
  cases h : row.coefficient <;>
    simp [SplitRow.residual, SplitRow.holds, termParity_append, termParity, h]

/-- Exact constrained projection on split sparse ANFs, before normalization. -/
theorem project_constrained_weighted_exact {n : ℕ}
    (pivot mixed : List (AffineTerm n)) (base : List (SquarefreeTerm n))
    (rows : List (SplitRow n)) (k : ℕ) (b : Fin n → Bool) :
    (∑ x : Bool, if (x == termParity (evalAffineTerm b) pivot) &&
        rows.all (fun row => row.holds x b) then
        (2 : ℤ) ^ k * sign (termParity (evalSquarefreeTerm b) base ^^
          (x && termParity (evalAffineTerm b) mixed)) else 0) =
      (if rows.all (fun row =>
        termParity (evalAffineTerm b) (row.residual pivot) == row.rhs) then
        (2 : ℤ) ^ k * sign (termParity (evalSquarefreeTerm b)
          (base ++ affineProduct mixed pivot)) else 0) := by
  simp only [SplitRow.residual_holds, termParity_append, eval_affineProduct]
  cases termParity (evalAffineTerm b) pivot <;> simp


/-- The elementary Gaussian-elimination row addition. Duplicate monomials
in the concatenation cancel under parity, exactly as coefficient XOR. -/
def SplitRow.add {n : ℕ} (r s : SplitRow n) : SplitRow n :=
  { coefficient := r.coefficient ^^ s.coefficient
    boundary := r.boundary ++ s.boundary
    rhs := r.rhs ^^ s.rhs }

def SplitRow.lhs {n : ℕ} (r : SplitRow n) (x : Bool)
    (b : Fin n → Bool) : Bool :=
  termParity (evalAffineTerm b) r.boundary ^^ (r.coefficient && x)

private theorem xor_distributes_mixed (a b c d x : Bool) :
    ((a ^^ b) ^^ ((c ^^ d) && x)) =
      ((a ^^ (c && x)) ^^ (b ^^ (d && x))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> decide

theorem SplitRow.add_lhs {n : ℕ} (r s : SplitRow n)
    (x : Bool) (b : Fin n → Bool) :
    (r.add s).lhs x b = (r.lhs x b ^^ s.lhs x b) := by
  change ((termParity (evalAffineTerm b) (r.boundary ++ s.boundary)) ^^
      ((r.coefficient ^^ s.coefficient) && x)) =
    ((termParity (evalAffineTerm b) r.boundary ^^ (r.coefficient && x)) ^^
      (termParity (evalAffineTerm b) s.boundary ^^ (s.coefficient && x)))
  rw [termParity_append]
  exact xor_distributes_mixed _ _ _ _ _

private theorem xor_equations_preserve (p q a b : Bool) :
    ((p == a) && (q == b)) =
      ((p == a) && ((p ^^ q) == (a ^^ b))) := by
  cases p <;> cases q <;> cases a <;> cases b <;> decide

/-- The solution predicate of two rows is unchanged when the second row
is replaced by its XOR with the first. This is valid at every assignment. -/
theorem SplitRow.add_preserves_feasibility {n : ℕ} (r s : SplitRow n)
    (x : Bool) (b : Fin n → Bool) :
    (r.holds x b && s.holds x b) =
      (r.holds x b && (r.add s).holds x b) := by
  change ((r.lhs x b == r.rhs) && (s.lhs x b == s.rhs)) =
      ((r.lhs x b == r.rhs) &&
        ((r.add s).lhs x b == (r.rhs ^^ s.rhs)))
  rw [r.add_lhs]
  exact xor_equations_preserve _ _ _ _

#print axioms IndependentETH.QuadraticBoundary.SplitRow.add_lhs
#print axioms IndependentETH.QuadraticBoundary.SplitRow.add_preserves_feasibility

/-- Shannon-style stitching of complementary supports in exact integers. -/
theorem stitch_sign (selector a b : Bool) :
    (if selector = true then (0 : ℤ) else sign a) +
      (if selector = true then sign b else 0) =
    sign (a ^^ (selector && (a ^^ b))) := by
  cases selector <;> cases a <;> cases b <;> decide

/-- Stitching is valid if an explicit quadratic witness is supplied. The
degree restriction cannot be inferred from an arbitrary phase expression. -/
theorem quadratic_stitch_exact {n : ℕ} (selector : Affine n)
    (left right combined : Quadratic n)
    (hdegree : ∀ b : Fin n → Bool,
      combined.eval b = (left.eval b ^^ (selector.eval b &&
        (left.eval b ^^ right.eval b))))
    (b : Fin n → Bool) :
    (if selector.eval b = true then (0 : ℤ) else sign (left.eval b)) +
      (if selector.eval b = true then sign (right.eval b) else 0) =
        sign (combined.eval b) := by
  rw [hdegree b]
  exact stitch_sign (selector.eval b) (left.eval b) (right.eval b)

/-- Two different supported modes collapse to one quadratic phase. -/
theorem two_to_one_example (b₀ b₁ : Bool) :
    (if b₀ = true then (0 : ℤ) else 1) +
      (if b₀ = true then sign b₁ else 0) =
        sign (b₀ && b₁) := by
  cases b₀ <;> cases b₁ <;> decide


/-!
## Constructive quadratic decomposition

An ANF on a distinguished internal variable x and n boundary variables
is an XOR of constants, linear variables and degree-two monomials.
The split procedure is executable structural recursion, not a
noncomputable existential choice.
-/

namespace Syntax

inductive AffExpr (n : ℕ) where
  | constant : Bool → AffExpr n
  | variable : Fin n → AffExpr n
  | xor : AffExpr n → AffExpr n → AffExpr n

def AffExpr.eval {n : ℕ} (a : AffExpr n) (b : Fin n → Bool) : Bool :=
  match a with
  | .constant c => c
  | .variable i => b i
  | .xor l r => l.eval b ^^ r.eval b

/-- Quadratic degree is a syntactic invariant, not a runtime guess. -/
inductive QuadExpr (n : ℕ) where
  | affine : AffExpr n → QuadExpr n
  | product : AffExpr n → AffExpr n → QuadExpr n
  | xor : QuadExpr n → QuadExpr n → QuadExpr n

def QuadExpr.eval {n : ℕ} (q : QuadExpr n) (b : Fin n → Bool) : Bool :=
  match q with
  | .affine a => a.eval b
  | .product a c => a.eval b && c.eval b
  | .xor l r => l.eval b ^^ r.eval b

/-- none is the distinguished internal variable, some i an exterior bit. -/
inductive FullPhase (n : ℕ) where
  | constant : Bool → FullPhase n
  | variable : Option (Fin n) → FullPhase n
  | product : Option (Fin n) → Option (Fin n) → FullPhase n
  | xor : FullPhase n → FullPhase n → FullPhase n

def bit {n : ℕ} (x : Bool) (b : Fin n → Bool) : Option (Fin n) → Bool
  | none => x
  | some i => b i

def FullPhase.eval {n : ℕ} (q : FullPhase n) (x : Bool)
    (b : Fin n → Bool) : Bool :=
  match q with
  | .constant c => c
  | .variable i => bit x b i
  | .product i j => bit x b i && bit x b j
  | .xor l r => l.eval x b ^^ r.eval x b

structure Split (n : ℕ) where
  base : QuadExpr n
  mixed : AffExpr n

def Split.eval {n : ℕ} (p : Split n) (x : Bool)
    (b : Fin n → Bool) : Bool :=
  p.base.eval b ^^ (x && p.mixed.eval b)

def Split.xor {n : ℕ} (p q : Split n) : Split n :=
  ⟨.xor p.base q.base, .xor p.mixed q.mixed⟩

def FullPhase.split {n : ℕ} : FullPhase n → Split n
  | .constant c => ⟨.affine (.constant c), .constant false⟩
  | .variable none => ⟨.affine (.constant false), .constant true⟩
  | .variable (some i) => ⟨.affine (.variable i), .constant false⟩
  | .product none none => ⟨.affine (.constant false), .constant true⟩
  | .product none (some j) => ⟨.affine (.constant false), .variable j⟩
  | .product (some i) none => ⟨.affine (.constant false), .variable i⟩
  | .product (some i) (some j) =>
      ⟨.product (.variable i) (.variable j), .constant false⟩
  | .xor l r => (l.split).xor r.split

private theorem xor_split_identity (base₁ base₂ mixed₁ mixed₂ x : Bool) :
    ((base₁ ^^ base₂) ^^ (x && (mixed₁ ^^ mixed₂))) =
      ((base₁ ^^ (x && mixed₁)) ^^ (base₂ ^^ (x && mixed₂))) := by
  cases base₁ <;> cases base₂ <;> cases mixed₁ <;>
    cases mixed₂ <;> cases x <;> decide

/-- Every syntactic quadratic ANF has an exact constructible
boundary-quadratic plus mixed-affine decomposition. -/
theorem FullPhase.split_correct {n : ℕ} (q : FullPhase n)
    (x : Bool) (b : Fin n → Bool) :
    q.split.eval x b = q.eval x b := by
  induction q with
  | constant c =>
      cases c <;> cases x <;>
        simp [FullPhase.split, Split.eval, QuadExpr.eval, AffExpr.eval, FullPhase.eval]
  | «variable» i =>
      cases i with
      | none =>
          cases x <;> simp [FullPhase.split, Split.eval,
            QuadExpr.eval, AffExpr.eval, FullPhase.eval, bit]
      | some j =>
          cases x <;> cases b j <;>
            simp [FullPhase.split, Split.eval, QuadExpr.eval,
              AffExpr.eval, FullPhase.eval, bit]
  | product i j =>
      cases i with
      | none =>
          cases j with
          | none =>
              cases x <;> simp [FullPhase.split, Split.eval,
                QuadExpr.eval, AffExpr.eval, FullPhase.eval, bit]
          | some j =>
              cases x <;> cases b j <;>
                simp [FullPhase.split, Split.eval, QuadExpr.eval,
                  AffExpr.eval, FullPhase.eval, bit]
      | some i =>
          cases j with
          | none =>
              cases x <;> cases b i <;>
                simp [FullPhase.split, Split.eval, QuadExpr.eval,
                  AffExpr.eval, FullPhase.eval, bit]
          | some j =>
              cases x <;> cases b i <;> cases b j <;>
                simp [FullPhase.split, Split.eval, QuadExpr.eval,
                  AffExpr.eval, FullPhase.eval, bit]
  | xor l r hl hr =>
      change ((l.split.base.eval b ^^ r.split.base.eval b) ^^
          (x && (l.split.mixed.eval b ^^ r.split.mixed.eval b))) =
          (l.eval x b ^^ r.eval x b)
      rw [← hl, ← hr]
      exact xor_split_identity _ _ _ _ _

/-- Exact free elimination for every quadratic monomial syntax. -/
theorem FullPhase.project_exact {n : ℕ} (q : FullPhase n)
    (b : Fin n → Bool) :
    (∑ x : Bool, sign (q.eval x b)) =
      if q.split.mixed.eval b = true then 0
      else 2 * sign (q.split.base.eval b) := by
  calc
    (∑ x : Bool, sign (q.eval x b)) =
        ∑ x : Bool, sign (q.split.eval x b) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [q.split_correct x b]
    _ = _ := sum_sign_xor (q.split.base.eval b) (q.split.mixed.eval b)

/-- A forced internal bit has one extension, not two, at each exterior
assignment. This is an exact integer sum in every context. -/
theorem forced_projection_exact {n : ℕ} (p : Split n)
    (forced : AffExpr n) (feasible : (Fin n → Bool) → Bool)
    (k : ℕ) (b : Fin n → Bool) :
    (∑ x : Bool, if x = forced.eval b ∧ feasible b = true then
       (2 : ℤ) ^ k * sign (p.eval x b) else 0) =
      if feasible b = true then
        (2 : ℤ) ^ k * sign (p.eval (forced.eval b) b) else 0 := by
  cases hf : feasible b <;> cases hx : forced.eval b <;>
    simp [Fintype.sum_bool, hf, hx]

/-- Substitution is syntactically quadratic, not merely semantically equal
to an unbounded formula. -/
def Split.substitute {n : ℕ} (p : Split n)
    (forced : AffExpr n) : QuadExpr n :=
  .xor p.base (.product forced p.mixed)

theorem Split.substitute_correct {n : ℕ} (p : Split n)
    (forced : AffExpr n) (b : Fin n → Bool) :
    (p.substitute forced).eval b = p.eval (forced.eval b) b := by
  rfl

theorem forced_projection_quadratic {n : ℕ} (p : Split n)
    (forced : AffExpr n) (feasible : (Fin n → Bool) → Bool)
    (k : ℕ) (b : Fin n → Bool) :
    (∑ x : Bool, if x = forced.eval b ∧ feasible b = true then
       (2 : ℤ) ^ k * sign (p.eval x b) else 0) =
      if feasible b = true then
        (2 : ℤ) ^ k * sign ((p.substitute forced).eval b) else 0 := by
  rw [forced_projection_exact, p.substitute_correct]

#print axioms IndependentETH.QuadraticBoundary.Syntax.FullPhase.split_correct
#print axioms IndependentETH.QuadraticBoundary.Syntax.FullPhase.project_exact
#print axioms IndependentETH.QuadraticBoundary.Syntax.forced_projection_exact
#print axioms IndependentETH.QuadraticBoundary.Syntax.Split.substitute_correct
#print axioms IndependentETH.QuadraticBoundary.Syntax.forced_projection_quadratic

end Syntax

#print axioms IndependentETH.QuadraticBoundary.sum_sign_xor
#print axioms IndependentETH.QuadraticBoundary.project_free_exact
#print axioms IndependentETH.QuadraticBoundary.project_free_weighted_exact
#print axioms IndependentETH.QuadraticBoundary.project_constrained_weighted_exact
#print axioms IndependentETH.QuadraticBoundary.quadratic_stitch_exact
#print axioms IndependentETH.QuadraticBoundary.two_to_one_example

end IndependentETH.QuadraticBoundary
