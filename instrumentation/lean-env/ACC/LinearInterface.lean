import Mathlib
import ACC.Circuit

/-!
# Exact finite linear boundary interfaces

This is a second certified ACC representation, strictly more expressive
than quotienting states with identical outgoing signatures.

A state row is a finite linear combination of reusable basis functions.
The soundness property is UNIFORM over all external contexts.  Weight
aggregation, arbitrary finite linear continuation maps, and separated
tensor products preserve it.  None of these identities asserts that a
small basis can always be found efficiently.
-/

namespace ACC.LinearInterface

open scoped BigOperators

/-- A proof-carrying exact factorization of a boundary table.
    The source state and mode sets are finite, but Context itself need not
    be finite. Integer coefficients make the certificate valid without
    rational division or assumptions about fields. -/
structure Interface (State Mode Context : Type*)
    [DecidableEq State] [DecidableEq Mode] where
  states : Finset State
  modes : Finset Mode
  row : State → Context → ℤ
  coeff : State → Mode → ℤ
  basis : Mode → Context → ℤ
  reconstruct : ∀ s ∈ states, ∀ context,
    row s context =
      ∑ mode ∈ modes, coeff s mode * basis mode context

namespace Interface

variable {S M C : Type*} [DecidableEq S] [DecidableEq M]

/-- Ordinary state enumeration, used only as the semantic reference. -/
def weightedValue (I : Interface S M C) (weight : S → ℤ)
    (context : C) : ℤ :=
  ∑ s ∈ I.states, weight s * I.row s context

/-- The exact result of pushing weights through the certified basis. -/
def compressedCoeff (I : Interface S M C) (weight : S → ℤ)
    (mode : M) : ℤ :=
  ∑ s ∈ I.states, weight s * I.coeff s mode

def compressedValue (I : Interface S M C) (weight : S → ℤ)
    (context : C) : ℤ :=
  ∑ mode ∈ I.modes,
    I.compressedCoeff weight mode * I.basis mode context

/-- Uniform equality at ALL contexts, including contexts not present in
    any finite test sample. It requires only the factorization certificate. -/
theorem weighted_correct (I : Interface S M C) (weight : S → ℤ)
    (context : C) :
    I.weightedValue weight context =
      I.compressedValue weight context := by
  classical
  unfold weightedValue compressedValue compressedCoeff
  calc
    (∑ s ∈ I.states, weight s * I.row s context) =
      ∑ s ∈ I.states, ∑ mode ∈ I.modes,
        weight s * (I.coeff s mode * I.basis mode context) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [I.reconstruct s hs context, Finset.mul_sum]
    _ = ∑ mode ∈ I.modes, ∑ s ∈ I.states,
        weight s * (I.coeff s mode * I.basis mode context) :=
          Finset.sum_comm
    _ = ∑ mode ∈ I.modes,
        (∑ s ∈ I.states, weight s * I.coeff s mode) *
          I.basis mode context := by
      apply Finset.sum_congr rfl
      intro mode hm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      ring

/-- Any finite linear continuation of the boundary function preserves
    the SAME mode set and the SAME state coefficients. The new basis
    functions are obtained by applying the continuation to old modes. -/
def transfer (I : Interface S M C)
    {D : Type*} (contexts : Finset C) (kernel : D → C → ℤ) :
    Interface S M D where
  states := I.states
  modes := I.modes
  row := fun s d =>
    ∑ context ∈ contexts, kernel d context * I.row s context
  coeff := I.coeff
  basis := fun mode d =>
    ∑ context ∈ contexts, kernel d context * I.basis mode context
  reconstruct := by
    intro s hs d
    calc
      (∑ context ∈ contexts, kernel d context * I.row s context) =
        ∑ context ∈ contexts, ∑ mode ∈ I.modes,
          kernel d context * (I.coeff s mode * I.basis mode context) := by
          apply Finset.sum_congr rfl
          intro context hc
          rw [I.reconstruct s hs context, Finset.mul_sum]
      _ = ∑ mode ∈ I.modes, ∑ context ∈ contexts,
          kernel d context * (I.coeff s mode * I.basis mode context) :=
            Finset.sum_comm
      _ = ∑ mode ∈ I.modes, I.coeff s mode *
          ∑ context ∈ contexts,
            kernel d context * I.basis mode context := by
          apply Finset.sum_congr rfl
          intro mode hm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro context hc
          ring

@[simp] theorem transfer_modes (I : Interface S M C)
    {D : Type*} (contexts : Finset C) (kernel : D → C → ℤ) :
    (I.transfer contexts kernel).modes = I.modes := rfl

/-- Separated products of boundary interfaces are certified by tensoring
    their basis modes. The width multiplies, which can itself be
    exponential across many merges: this is closure, not a speed claim. -/
def tensor {S' M' C' : Type*}
    [DecidableEq S'] [DecidableEq M']
    (I : Interface S M C) (J : Interface S' M' C') :
    Interface (S × S') (M × M') (C × C') where
  states := I.states.product J.states
  modes := I.modes.product J.modes
  row := fun st ctx => I.row st.1 ctx.1 * J.row st.2 ctx.2
  coeff := fun st mode => I.coeff st.1 mode.1 * J.coeff st.2 mode.2
  basis := fun mode ctx => I.basis mode.1 ctx.1 * J.basis mode.2 ctx.2
  reconstruct := by
    rintro ⟨s,t⟩ hst ⟨c,d⟩
    obtain ⟨hs,ht⟩ := Finset.mem_product.mp hst
    change I.row s c * J.row t d =
      ∑ mode ∈ I.modes.product J.modes,
        (I.coeff s mode.1 * J.coeff t mode.2) *
          (I.basis mode.1 c * J.basis mode.2 d)
    rw [Finset.sum_product]
    calc
      I.row s c * J.row t d =
        (∑ mode ∈ I.modes, I.coeff s mode * I.basis mode c) *
        (∑ mode ∈ J.modes, J.coeff t mode * J.basis mode d) := by
          rw [I.reconstruct s hs c, J.reconstruct t ht d]
      _ = ∑ mode ∈ I.modes, ∑ mode' ∈ J.modes,
        (I.coeff s mode * J.coeff t mode') *
          (I.basis mode c * J.basis mode' d) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro mode hm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro mode' hm'
          ring

@[simp] theorem tensor_modes {S' M' C' : Type*}
    [DecidableEq S'] [DecidableEq M']
    (I : Interface S M C) (J : Interface S' M' C') :
    (I.tensor J).modes = I.modes.product J.modes := rfl

/-- A finite, explicitly checkable basis certificate. The caller supplies
    the state and context tables; no unbounded theorem search is performed. -/
def checkFinite {C' : Type*} [DecidableEq C']
    (states : Finset S) (modes : Finset M) (contexts : Finset C')
    (row : S → C' → ℤ) (coeff : S → M → ℤ)
    (basis : M → C' → ℤ) : Bool :=
  decide (∀ s ∈ states, ∀ c ∈ contexts,
    row s c = ∑ mode ∈ modes, coeff s mode * basis mode c)

theorem checkFinite_sound {C' : Type*} [DecidableEq C']
    (states : Finset S) (modes : Finset M) (contexts : Finset C')
    (row : S → C' → ℤ) (coeff : S → M → ℤ)
    (basis : M → C' → ℤ)
    (h : checkFinite states modes contexts row coeff basis = true) :
    ∀ s ∈ states, ∀ c ∈ contexts,
      row s c = ∑ mode ∈ modes, coeff s mode * basis mode c := by
  change decide (∀ s ∈ states, ∀ c ∈ contexts,
    row s c = ∑ mode ∈ modes, coeff s mode * basis mode c) = true at h
  exact of_decide_eq_true h

/-- For a finite, FULL context type, passing the table checker becomes
    a proof of context-uniform reconstruction. A sampled subset would not. -/
def fromChecked {C' : Type*} [Fintype C'] [DecidableEq C']
    (states : Finset S) (modes : Finset M)
    (row : S → C' → ℤ) (coeff : S → M → ℤ)
    (basis : M → C' → ℤ)
    (h : checkFinite states modes (Finset.univ : Finset C')
      row coeff basis = true) : Interface S M C' where
  states := states
  modes := modes
  row := row
  coeff := coeff
  basis := basis
  reconstruct := by
    intro s hs c
    exact checkFinite_sound states modes Finset.univ row coeff basis h
      s hs c (Finset.mem_univ c)

end Interface

/-! ## A concrete strict 3-state to 2-mode example -/

/-- Three distinct outgoing rows, indexed by two boundary contexts. -/
def threeRow (state : Fin 3) (context : Bool) : ℤ :=
  if state = 0 then (if context then 0 else 1)
  else if state = 1 then (if context then 1 else 0)
  else 1

/-- First two rows are basis vectors; the third is their sum. -/
def threeCoeff (state : Fin 3) (mode : Bool) : ℤ :=
  if state = 0 then (if mode then 0 else 1)
  else if state = 1 then (if mode then 1 else 0)
  else 1

def twoBasis (mode context : Bool) : ℤ :=
  if mode = context then 1 else 0

/-- Proof-producing construction from an executable exhaustive check
    on the FULL finite state/context table. -/
def threeIntoTwo : Interface (Fin 3) Bool Bool :=
  Interface.fromChecked Finset.univ Finset.univ
    threeRow threeCoeff twoBasis (by decide)

theorem three_row_01 : threeRow 0 ≠ threeRow 1 := by
  intro h
  have hx := congrFun h false
  norm_num [threeRow] at hx

theorem three_row_02 : threeRow 0 ≠ threeRow 2 := by
  intro h
  have hx := congrFun h true
  norm_num [threeRow] at hx

theorem three_row_12 : threeRow 1 ≠ threeRow 2 := by
  intro h
  have hx := congrFun h false
  norm_num [threeRow] at hx

/-- Three genuinely distinct source states, only two exact basis modes. -/
theorem threeIntoTwo_strict :
    threeIntoTwo.modes.card < threeIntoTwo.states.card := by
  decide

/-- Works with arbitrary integer weights, even negative ones. -/
theorem threeIntoTwo_correct (weight : Fin 3 → ℤ) (context : Bool) :
    threeIntoTwo.weightedValue weight context =
      threeIntoTwo.compressedValue weight context :=
  threeIntoTwo.weighted_correct weight context

#print axioms ACC.LinearInterface.Interface.weighted_correct
#print axioms ACC.LinearInterface.Interface.transfer_modes
#print axioms ACC.LinearInterface.Interface.tensor_modes
#print axioms ACC.LinearInterface.Interface.checkFinite_sound
#print axioms ACC.LinearInterface.threeIntoTwo_strict
#print axioms ACC.LinearInterface.threeIntoTwo_correct

end ACC.LinearInterface
