import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Constructive coded arithmetic for the QueryStream leaf

A leaf first multiplies its restricted full-signature head sums in the
original nested truncated ring, then applies the additive marker readout.
The coefficient representation is the original executable RingProgram;
decoding and ring laws occur only in correctness theorems.

This is a numerical arithmetic boundary for supplied head-sum codes, not
an implementation of the head rescan or a whole-CNF evaluator.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamConstructiveLeaf

open scoped BigOperators
open SubexpSymbolicCost
open SqrtLog.TotalOrder
open SubexpLiftRing SubexpQuarticRing

variable {C R : Type*}

/-- Decode finite coefficient functions into the source's exact truncated type. -/
def decodeArray {n : ℕ} (decode : C → R) (a : Fin n → C) : Truncated R n :=
  ⟨fun i => decode (a i)⟩

/-- Out-of-range reads are the original program's zero code. -/
def readCode (ops : RingProgram C) {n : ℕ} (a : Fin n → C) (i : ℕ) : C :=
  if h : i < n then a ⟨i,h⟩ else ops.zeroRun.1

theorem readCode_correct [CommRing R] (ops : RepresentedRing C R)
    {n : ℕ} (a : Fin n → C) (i : ℕ) :
    ops.decode (readCode ops.program a i) = arrayCoeff (fun j => ops.decode (a j)) i := by
  by_cases h : i < n <;> simp [readCode, arrayCoeff, h, ops.zero_correct]

/-- One coefficient of convolution. The finite index list is exactly the
    antidiagonal of the requested output degree. Use the original measured
    scalar sum and multiplication, including their event charges. -/
def convolution (ops : RingProgram C) {n : ℕ} (a b : Fin n → C)
    (k : Fin n) : C × ℕ :=
  SqrtLog.RingProgram.sumRun ops
    (List.ofFn fun i : Fin (k.val + 1) =>
      ops.mulRun (readCode ops a i.val) (readCode ops b (k.val - i.val)))

theorem convolution_correct [CommRing R] (ops : RepresentedRing C R)
    {n : ℕ} (a b : Fin n → C) (k : Fin n) :
    ops.decode (convolution ops.program a b k).1 =
      (decodeArray ops.decode a * decodeArray ops.decode b).coeff k := by
  rw [convolution, SqrtLog.RingProgram.sumRun_correct, Truncated.coeff_mul]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, ops.mul_correct,
    readCode_correct, decodeArray]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun uv => arrayCoeff (fun i => ops.decode (a i)) uv.1 *
      arrayCoeff (fun i => ops.decode (b i)) uv.2) k.val,
    ← Fin.sum_univ_eq_sum_range] <;> rfl

/-- The code-level truncated-ring program. Tabulation materializes the output
    coefficients, and no semantic quotient-ring instance is executed. -/
def truncProgram (ops : RingProgram C) (n : ℕ) : RingProgram (Fin n → C) where
  zeroRun := SqrtLog.RingProgram.tabulateRun fun _ => ops.zeroRun
  oneRun := SqrtLog.RingProgram.tabulateRun fun i => if i.val = 0 then ops.oneRun else ops.zeroRun
  addRun a b := SqrtLog.RingProgram.tabulateRun fun i => ops.addRun (a i) (b i)
  mulRun a b := SqrtLog.RingProgram.tabulateRun fun k => convolution ops a b k
  negRun a := SqrtLog.RingProgram.tabulateRun fun i => ops.negRun (a i)

/-- Lift the source's coefficient representation through exactly one truncation.
    Only this proof-side record mentions the semantic ring. -/
noncomputable def representedTrunc [CommRing R] (ops : RepresentedRing C R)
    (n : ℕ) : RepresentedRing (Fin n → C) (Truncated R n) where
  decode := decodeArray ops.decode
  zeroRun := (truncProgram ops.program n).zeroRun
  oneRun := (truncProgram ops.program n).oneRun
  addRun := (truncProgram ops.program n).addRun
  mulRun := (truncProgram ops.program n).mulRun
  negRun := (truncProgram ops.program n).negRun
  zero_correct := by
    ext i
    simp [decodeArray, truncProgram, ops.zero_correct]
  one_correct := by
    ext i
    by_cases h : i.val = 0 <;>
      simp [decodeArray, truncProgram, h, ops.zero_correct, ops.one_correct]
  add_correct := by
    intro a b
    ext i
    simp [decodeArray, truncProgram, ops.add_correct]
  mul_correct := by
    intro a b
    ext i
    simpa only [decodeArray, truncProgram, SqrtLog.RingProgram.tabulateRun_eq]
      using convolution_correct ops a b i
  neg_correct := by
    intro a
    ext i
    simp [decodeArray, truncProgram, ops.neg_correct]

@[simp] theorem representedTrunc_program [CommRing R] (ops : RepresentedRing C R)
    (n : ℕ) : (representedTrunc ops n).program = truncProgram ops.program n := rfl

/-- Actual finite ordered product, with both multiplication and child costs. -/
def productRun (ops : RingProgram C) : List C → C × ℕ
  | [] => ops.oneRun
  | a :: as =>
    let rest := productRun ops as
    let out := ops.mulRun a rest.1
    (out.1, rest.2 + out.2 + 1)

theorem productRun_correct [CommRing R] (ops : RepresentedRing C R) (as : List C) :
    ops.decode (productRun ops.program as).1 = (as.map ops.decode).prod := by
  induction as with
  | nil => exact ops.one_correct
  | cons a as ih =>
    change ops.decode (ops.mulRun a (productRun ops.program as).1).1 = _
    rw [ops.mul_correct, ih]
    rfl

/-- Sum the retained shared-marker coefficients *after* multiplication.
    The result is the source's one-dimensional Taylor array. -/
def readoutRun (ops : RingProgram C) {t J : ℕ}
    (a : Fin t → Fin J → C) : (Fin J → C) × ℕ :=
  SqrtLog.RingProgram.tabulateRun fun z =>
    SqrtLog.RingProgram.sumRun ops (List.ofFn fun u : Fin t => (a u z, 0))

theorem readoutRun_correct [CommRing R] (ops : RepresentedRing C R) {t J : ℕ}
    (a : Fin t → Fin J → C) :
    decodeArray ops.decode (readoutRun ops.program a).1 =
      Dense.readout (decodeArray (decodeArray ops.decode) a) := by
  ext z
  rw [Dense.coeff_readout]
  simp only [decodeArray, readoutRun, SqrtLog.RingProgram.tabulateRun_eq,
    SqrtLog.RingProgram.sumRun_correct, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

/-- Numerical leaf contraction on supplied head-sum codes, in the source's
    marker/Taylor order. Both truncations remain in force until readout. -/
def leafRun (ops : RingProgram C) {t J : ℕ}
    (heads : List (Fin t → Fin J → C)) : (Fin J → C) × ℕ :=
  let product := productRun (truncProgram (truncProgram ops J) t) heads
  let output := readoutRun ops product.1
  (output.1, product.2 + output.2)

theorem leafRun_correct [CommRing R] (ops : RepresentedRing C R) {t J : ℕ}
    (heads : List (Fin t → Fin J → C)) :
    decodeArray ops.decode (leafRun ops.program heads).1 =
      Dense.readout ((heads.map (decodeArray (decodeArray ops.decode))).prod) := by
  rw [leafRun, readoutRun_correct]
  congr 1
  exact productRun_correct (representedTrunc (representedTrunc ops J) t) heads

/-- Indexed heads have the same finite product domain as the original
    `SignatureTupleRun.emittedValue`. The hypothesis is precisely the
    head-code correctness boundary, not an oracle for the final leaf. -/
theorem leafRun_correct_ofFn [CommRing R] (ops : RepresentedRing C R)
    {t J r : ℕ} (heads : Fin r → Fin t → Fin J → C)
    (values : Fin r → Dense R t J)
    (h : ∀ g, decodeArray (decodeArray ops.decode) (heads g) = values g) :
    decodeArray ops.decode (leafRun ops.program (List.ofFn heads)).1 =
      Dense.readout (∏ g : Fin r, values g) := by
  rw [leafRun_correct, List.map_ofFn, List.prod_ofFn]
  congr 1
  apply Finset.prod_congr rfl
  intro g _
  exact h g

/-- Specialization to the actual supplied-polynomial ternary model. The
    executable input is model data and paid scalar cache, not a noncomputable
    represented-ring record or a choice of a quotient representative. -/
def modelLeafRun (t : ℕ) {d J : ℕ}
    (a : SqrtLog.RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : SqrtLog.RingProgram.ScalarCache 3 t)
    (heads : List (Fin t → Fin J →
      SqrtLog.RingProgram.Code (SqrtLog.RingProgram.ScalarCode 3 t) d)) :=
  let prepared := SqrtLog.RingProgram.modelProgramRun t a M cache
  let result := leafRun prepared.1 heads
  (result.1, prepared.2 + result.2)

theorem modelLeafRun_correct (t : ℕ) (ht : 0 < t) {d J : ℕ} (hd : 0 < d)
    (a : SqrtLog.RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : SqrtLog.RingProgram.ScalarCache 3 t)
    (heads : List (Fin t → Fin J →
      SqrtLog.RingProgram.Code (SqrtLog.RingProgram.ScalarCode 3 t) d)) :
    let ops := SqrtLog.RingProgram.modelRing t ht hd a M cache
    decodeArray ops.decode (modelLeafRun t a M cache heads).1 =
      Dense.readout ((heads.map (decodeArray (decodeArray ops.decode))).prod) := by
  dsimp only
  simp only [modelLeafRun, SqrtLog.RingProgram.modelProgramRun_value]
  rw [← SqrtLog.RingProgram.modelRing_program t ht hd a M cache]
  exact leafRun_correct _ heads

section HeadDictionary

open SqrtLog.MomentsProgram
open TruncatedRingProgram

/-- Direct executable lookup of the original sparse key. Missing coefficients
    use the source zero code; retained zero records need not be removed. -/
def dictionaryCodes {n B d : ℕ}
    (zero : SqrtLog.RingProgram.Code (Word B) d)
    (entries : List (Product.Entry n B d)) (t J : ℕ) :
    Fin t → Fin J → SqrtLog.RingProgram.Code (Word B) d :=
  fun u z => (entries.lookup (⟨u.val, z.val, ∅⟩ : SqrtLog.Squarefree.Index (Fin n))).getD zero

/-- The original sparse fetch is a sum, so first-match lookup is sound
    precisely under the normalized distinct-key invariant. -/
theorem dictionaryCodes_correct {n B d t J : ℕ} [CommRing R]
    (decode : SqrtLog.RingProgram.Code (Word B) d → R)
    (zero : SqrtLog.RingProgram.Code (Word B) d) (hz : decode zero = 0)
    (entries : List (Product.Entry n B d))
    (hn : (SqrtLog.Squarefree.Sparse.keys entries).Nodup) :
    decodeArray (decodeArray decode) (dictionaryCodes zero entries t J) =
      rawValue t J decode entries := by
  ext u z
  rw [rawValue_coeff]
  let key : SqrtLog.Squarefree.Index (Fin n) := ⟨u.val, z.val, ∅⟩
  have hf := SqrtLog.Squarefree.Program.fetch_eq_lookup
    (Dictionary.denoteTable decode entries) key
    (by simpa only [Dictionary.denoteTable_keys] using hn)
  rw [Dictionary.denoteTable_lookup] at hf
  change decode ((entries.lookup key).getD zero) =
    SqrtLog.Squarefree.Sparse.fetch key (Dictionary.denoteTable decode entries)
  cases he : entries.lookup key with
  | none => simpa [he, hz] using hf.symm
  | some x => simpa [he] using hf.symm

/-- Compose the actual normalized head dictionaries using the same
    coefficient program as the dense leaf kernel. -/
def dictionaryLeafRun {n B d t J r : ℕ}
    (ops : RingProgram (SqrtLog.RingProgram.Code (Word B) d))
    (heads : Fin r → List (Product.Entry n B d)) :=
  leafRun ops (List.ofFn (fun g => dictionaryCodes ops.zeroRun.1 (heads g) t J))

/-- Exact source dense head product and additive readout from the actual
    normalized sparse dictionaries. The head rescan producing them remains
    an independent upstream-to-executable obligation. -/
theorem dictionaryLeafRun_correct {n B d t J r : ℕ} [CommRing R]
    (ops : RepresentedRing (SqrtLog.RingProgram.Code (Word B) d) R)
    (heads : Fin r → List (Product.Entry n B d))
    (hn : ∀ g, (SqrtLog.Squarefree.Sparse.keys (heads g)).Nodup) :
    decodeArray ops.decode (dictionaryLeafRun (t := t) (J := J) ops.program heads).1 =
      Dense.readout (∏ g : Fin r, rawValue t J ops.decode (heads g)) := by
  unfold dictionaryLeafRun
  apply leafRun_correct_ofFn
  intro g
  exact dictionaryCodes_correct ops.decode ops.zeroRun.1 ops.zero_correct (heads g) (hn g)

#print axioms dictionaryCodes_correct
#print axioms dictionaryLeafRun_correct

end HeadDictionary

/-- Transparent arithmetic for regression tests. The production specialization
    above uses the original model program instead. -/
def intProgram : RingProgram ℤ where
  zeroRun := (0, 1)
  oneRun := (1, 1)
  addRun a b := (a + b, 1)
  mulRun a b := (a * b, 1)
  negRun a := (-a, 1)

def marker : Fin 2 → Fin 2 → ℤ :=
  fun u z => if u.val = 1 && z.val = 0 then 1 else 0

def onePlusMarker : Fin 2 → Fin 2 → ℤ :=
  fun _ z => if z.val = 0 then 1 else 0

-- Reading each marker separately gives 1, but their product is truncated to 0.
example : List.ofFn (leafRun intProgram [marker, marker]).1 = [0, 0] := by decide
example : List.ofFn (leafRun intProgram [onePlusMarker, onePlusMarker]).1 = [3, 0] := by decide
example : List.ofFn (leafRun intProgram (t := 2) (J := 2) []).1 = [1, 0] := by decide

#eval List.ofFn (leafRun intProgram [marker, marker]).1
#eval List.ofFn (leafRun intProgram [onePlusMarker, onePlusMarker]).1
#eval List.ofFn (leafRun intProgram (t := 2) (J := 2) []).1

#print axioms convolution_correct
#print axioms representedTrunc
#print axioms leafRun_correct
#print axioms leafRun_correct_ofFn
#print axioms modelLeafRun_correct

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamConstructiveLeaf
