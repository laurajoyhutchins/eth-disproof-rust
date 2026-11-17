import Mathlib

/-!
# Exact tensor-factorized port operators

A full-rank identity kernel on n Boolean ports has 2^n rows, but its
representation needs only n two-by-two wire tables, and its point-query
evaluation uses a product over n wires. We prove both facts exactly.

An arbitrary factorized input remains factorized under any tensor product
of two-by-two wire maps: the output factors are two-term local sums.
No materialized 2^n-by-2^n matrix is required for that representation.

These are mathematical semantics; Lean's Finset and Fintype enumeration
here is not a resource-certified runtime. Non-factorized input functions
remain a separate worst-case challenge.
-/

namespace ACC.FactoredOperator

open scoped BigOperators

/-- Explicit integer entries of one Boolean input/output wire. -/
structure WireMatrix where
  ff : ℤ
  ft : ℤ
  tf : ℤ
  tt : ℤ

def WireMatrix.lookup (w : WireMatrix) (out input : Bool) : ℤ :=
  match out, input with
  | false, false => w.ff
  | false, true => w.ft
  | true, false => w.tf
  | true, true => w.tt

def WireMatrix.identity : WireMatrix where
  ff := 1
  ft := 0
  tf := 0
  tt := 1

theorem WireMatrix.identity_lookup (out input : Bool) :
    WireMatrix.identity.lookup out input =
      if out = input then (1 : ℤ) else 0 := by
  cases out <;> cases input <;> rfl

/-- A succinct operator is exactly one table per port. This is a
    factored representation, not an uncharged full-matrix oracle. -/
structure TensorKernel (n : ℕ) where
  wire : Fin n → WireMatrix

/-- Matrix-entry semantics of a tensor product of two-by-two kernels. -/
def TensorKernel.eval {n : ℕ} (K : TensorKernel n)
    (out input : Fin n → Bool) : ℤ :=
  ∏ i : Fin n, (K.wire i).lookup (out i) (input i)

def TensorKernel.identity (n : ℕ) : TensorKernel n :=
  ⟨fun _ => WireMatrix.identity⟩

theorem TensorKernel.identity_eval (n : ℕ)
    (out input : Fin n → Bool) :
    (TensorKernel.identity n).eval out input =
      if out = input then (1 : ℤ) else 0 := by
  classical
  by_cases heq : out = input
  · subst input
    simp [TensorKernel.eval, TensorKernel.identity,
      WireMatrix.identity_lookup]
  · rw [if_neg heq]
    have hdiff : ∃ i : Fin n, out i ≠ input i := by
      by_contra hn
      push_neg at hn
      exact heq (funext hn)
    rcases hdiff with ⟨i, hi⟩
    change (∏ j : Fin n,
      WireMatrix.identity.lookup (out j) (input j)) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      rw [WireMatrix.identity_lookup]
      simp [hi])

/-- The original port identity is full rank over the rationals.
    Its matrix is 2^n square but is described by n identity wire tables. -/
theorem TensorKernel.identity_rank (n : ℕ) :
    Matrix.rank
      (fun out input : Fin n → Bool =>
        ((TensorKernel.identity n).eval out input : ℚ)) =
      2 ^ n := by
  classical
  have hmatrix :
      (fun out input : Fin n → Bool =>
        ((TensorKernel.identity n).eval out input : ℚ)) =
        (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℚ) := by
    ext out input
    rw [TensorKernel.identity_eval]
    split_ifs <;> simp_all [Matrix.one_apply]
  rw [hmatrix, Matrix.rank_one]
  simp [Fintype.card_fun]

/-- No strict row-identification quotient preserves an unrestricted
    identity kernel. This is the precise boundary of equality-class
    state compression, independent of tensor-product syntax. -/
theorem TensorKernel.identity_forces_injective (n : ℕ)
    {Tag : Type*} (encode : (Fin n → Bool) → Tag)
    (represent : Tag → Fin n → Bool)
    (h : ∀ x y, (TensorKernel.identity n).eval x y =
      (TensorKernel.identity n).eval (represent (encode x)) y) :
    Function.Injective encode := by
  have recover (x : Fin n → Bool) : represent (encode x) = x := by
    have hx := h x x
    simp only [TensorKernel.identity_eval] at hx
    have hx' : (1 : ℤ) =
        if represent (encode x) = x then 1 else 0 := by
      simpa using hx
    by_contra hne
    simp [hne] at hx'
  intro x y hxy
  calc
    x = represent (encode x) := (recover x).symm
    _ = represent (encode y) := by rw [hxy]
    _ = y := recover y

/-- For an arbitrary unstructured input table, the denotation is
    the full (potentially exponential) contraction. -/
noncomputable def TensorKernel.apply {n : ℕ} (K : TensorKernel n)
    (input : (Fin n → Bool) → ℤ) (out : Fin n → Bool) : ℤ :=
  ∑ x ∈ Fintype.piFinset
    (fun _ : Fin n => (Finset.univ : Finset Bool)),
    K.eval out x * input x

/-- Factorized input is represented by only two coefficients per port. -/
def productInput {n : ℕ} (v : Fin n → Bool → ℤ)
    (input : Fin n → Bool) : ℤ :=
  ∏ i : Fin n, v i (input i)

/-- The non-enumerating *symbolic* output of the tensor operator,
    as a product of two-term sums. -/
def TensorKernel.applyProduct {n : ℕ} (K : TensorKernel n)
    (v : Fin n → Bool → ℤ) (out : Fin n → Bool) : ℤ :=
  ∏ i : Fin n, ∑ bit ∈ (Finset.univ : Finset Bool),
    (K.wire i).lookup (out i) bit * v i bit

/-- Exact semantics of product-state execution. The proof relates the
    symbolic O(n) count of local tables to the full exponential sum,
    but does not assert a bit-operation bound for arbitrary integers. -/
theorem TensorKernel.applyProduct_correct {n : ℕ}
    (K : TensorKernel n) (v : Fin n → Bool → ℤ)
    (out : Fin n → Bool) :
    K.apply (productInput v) out = K.applyProduct v out := by
  classical
  unfold TensorKernel.apply TensorKernel.applyProduct
  simp only [TensorKernel.eval, productInput]
  calc
    (∑ x ∈ Fintype.piFinset
      (fun _ : Fin n => (Finset.univ : Finset Bool)),
      (∏ i : Fin n, (K.wire i).lookup (out i) (x i)) *
      (∏ i : Fin n, v i (x i))) =
      ∑ x ∈ Fintype.piFinset
        (fun _ : Fin n => (Finset.univ : Finset Bool)),
        ∏ i : Fin n,
          (K.wire i).lookup (out i) (x i) * v i (x i) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (Finset.prod_mul_distrib).symm
    _ = ∏ i : Fin n, ∑ bit ∈ (Finset.univ : Finset Bool),
         (K.wire i).lookup (out i) bit * v i bit := by
      exact Finset.sum_prod_piFinset
        (Finset.univ : Finset Bool)
        (fun i bit => (K.wire i).lookup (out i) bit * v i bit)

/-- Identity acts on product input without constructing the matrix. -/
theorem TensorKernel.identity_applyProduct (n : ℕ)
    (v : Fin n → Bool → ℤ) (out : Fin n → Bool) :
    (TensorKernel.identity n).applyProduct v out =
      productInput v out := by
  classical
  unfold TensorKernel.applyProduct productInput
  apply Finset.prod_congr rfl
  intro i hi
  simp [TensorKernel.identity, WireMatrix.identity_lookup]

/-- This counts LOCAL table entries in the tensor representation,
    not the number of integers in the exponentially large matrix. -/
def TensorKernel.tableEntryCount (n : ℕ) : ℕ := 4 * n

theorem TensorKernel.identity_tableEntryCount (n : ℕ) :
    TensorKernel.tableEntryCount n = 4 * n := rfl

/-! A portfolio must not confuse estimated scores with verified bit cost. -/

/-- A semantics-certified candidate. The score is an EXPLICIT ESTIMATE,
    not a theorem about actual runtime or an oracle. -/
structure EstimatedCandidate (C : Type*) (spec : C → ℤ) where
  run : C → ℤ
  exact : ∀ context, run context = spec context
  estimatedTotalCost : ℕ

/-- Conservative optimization rule: selection never breaks semantic
    correctness, even if estimated costs are inaccurate. -/
def EstimatedCandidate.choose {C : Type*} {spec : C → ℤ}
    (a b : EstimatedCandidate C spec) : EstimatedCandidate C spec :=
  if a.estimatedTotalCost ≤ b.estimatedTotalCost then a else b

theorem EstimatedCandidate.choose_exact {C : Type*} {spec : C → ℤ}
    (a b : EstimatedCandidate C spec) (context : C) :
    (EstimatedCandidate.choose a b).run context = spec context := by
  by_cases h : a.estimatedTotalCost ≤ b.estimatedTotalCost
  · simp [EstimatedCandidate.choose, h, a.exact]
  · simp [EstimatedCandidate.choose, h, b.exact]

theorem EstimatedCandidate.choose_estimated_le_left
    {C : Type*} {spec : C → ℤ}
    (a b : EstimatedCandidate C spec) :
    (EstimatedCandidate.choose a b).estimatedTotalCost ≤
      a.estimatedTotalCost := by
  by_cases h : a.estimatedTotalCost ≤ b.estimatedTotalCost
  · simp [EstimatedCandidate.choose, h]
  · simp [EstimatedCandidate.choose, h]
    exact Nat.le_of_not_ge h

theorem EstimatedCandidate.choose_estimated_le_right
    {C : Type*} {spec : C → ℤ}
    (a b : EstimatedCandidate C spec) :
    (EstimatedCandidate.choose a b).estimatedTotalCost ≤
      b.estimatedTotalCost := by
  by_cases h : a.estimatedTotalCost ≤ b.estimatedTotalCost
  · simp [EstimatedCandidate.choose, h]
  · simp [EstimatedCandidate.choose, h]

#print axioms ACC.FactoredOperator.TensorKernel.identity_rank
#print axioms ACC.FactoredOperator.TensorKernel.identity_forces_injective
#print axioms ACC.FactoredOperator.TensorKernel.applyProduct_correct
#print axioms ACC.FactoredOperator.TensorKernel.identity_applyProduct
#print axioms ACC.FactoredOperator.EstimatedCandidate.choose_exact

end ACC.FactoredOperator
