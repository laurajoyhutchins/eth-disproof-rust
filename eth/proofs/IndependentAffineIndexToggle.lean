import Mathlib

/-!
# Source-name lookup and row-toggle refinement

The Rust affine checker registers each declared variable in a
name-to-column map, then toggles the corresponding dense Boolean bit
for *each occurrence* in an equation. The mathematical indexing seam:

1. Declared column names are pairwise distinct.
2. Successful lookup returns a column whose registered name is the
   requested name.
3. An update toggles precisely that column.

Under those explicit preconditions, this module proves that arbitrary
sequences of index-based toggles produce the same full coefficient row
as occurrence-parity semantics, including repeated names.

This is a universal proof of the *specified lookup/update algorithm*
under a lookup witness, not verification of Rust BTreeMap internals,
its UTF-8 parser, or the compiled Rust binary.
-/

namespace IndependentETH.AffineIndexToggle

abbrev Name := List Nat

/-- Rust's dense row update at one validated column. -/
def toggleIndex {n : Nat} (index : Fin n)
    (row : Fin n → Bool) : Fin n → Bool :=
  fun col => row col ^^ decide (col = index)

/-- Direct, name-based parity semantics, independent of indices. -/
def toggleName {n : Nat} (names : Fin n → Name)
    (row : Fin n → Bool) (name : Name) : Fin n → Bool :=
  fun col => row col ^^ decide (name = names col)

/-- A successful lookup identifying a registered name toggles exactly
the same row coordinate as name comparison, provided column names are
unique. The essential lookup obligation is visible as an assumption. -/
theorem toggle_index_eq_toggle_name
    {n : Nat} (names : Fin n → Name)
    (hUnique : Function.Injective names)
    (row : Fin n → Bool) (name : Name) (index : Fin n)
    (hLookup : names index = name) :
    toggleIndex index row = toggleName names row name := by
  funext col
  by_cases h : col = index
  · subst col
    simp [toggleIndex, toggleName, hLookup]
  · have hn : name ≠ names col := by
      intro heq
      have hc : names index = names col := by rw [hLookup, heq]
      exact h (hUnique hc).symm
    simp [toggleIndex, toggleName, h, hn]

/-- Folded lookup-based row construction and name-based construction
agree for any occurrence list, even with duplicate occurrences.
The source-domain condition rules out undeclared variable names. -/
theorem foldl_lookup_eq_named
    {n : Nat} (names : Fin n → Name)
    (hUnique : Function.Injective names)
    (lookup : Name → Fin n)
    (occurrences : List Name)
    (hDeclared : ∀ name ∈ occurrences, names (lookup name) = name)
    (initial : Fin n → Bool) :
    occurrences.foldl (fun row name => toggleIndex (lookup name) row) initial =
    occurrences.foldl (toggleName names) initial := by
  induction occurrences generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [toggle_index_eq_toggle_name names hUnique initial head
        (lookup head) (hDeclared head (by simp))]
      apply ih
      intro name hmem
      exact hDeclared name (by simp [hmem])

/-- Projecting the name-based vector construction onto any coordinate
is the same as folding XOR over all source occurrences. -/
theorem foldl_named_at
    {n : Nat} (names : Fin n → Name)
    (occurrences : List Name) (initial : Fin n → Bool)
    (col : Fin n) :
    (occurrences.foldl (toggleName names) initial) col =
      occurrences.foldl (fun parity name =>
        parity ^^ decide (name = names col)) (initial col) := by
  induction occurrences generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rfl

/-- Exact indexed source matrix construction for *every* declared
variable count and source occurrence list. No enumeration of assignments
or restriction to a fixed fixture size is involved. -/
theorem indexed_matrix_row_correct
    {n : Nat} (names : Fin n → Name)
    (hUnique : Function.Injective names)
    (lookup : Name → Fin n)
    (occurrences : List Name)
    (hDeclared : ∀ name ∈ occurrences, names (lookup name) = name)
    (col : Fin n) :
    (occurrences.foldl
      (fun row name => toggleIndex (lookup name) row)
      (fun _ => false)) col =
    occurrences.foldl
      (fun parity name => parity ^^ decide (name = names col))
      false := by
  rw [foldl_lookup_eq_named names hUnique lookup occurrences hDeclared]
  exact foldl_named_at names occurrences (fun _ => false) col

/-- Repeated occurrences toggle any indexed coefficient twice, leaving
it unchanged, including when the repeated variable is elsewhere. -/
theorem duplicate_index_toggle
    {n : Nat} (index : Fin n) (row : Fin n → Bool) :
    toggleIndex index (toggleIndex index row) = row := by
  funext col
  by_cases h : col = index
  · simp [toggleIndex, h]
  · simp [toggleIndex, h]


/-!
## Checked raw-index admission

The independent Rust verifier now validates each BTreeMap-supplied
candidate index against the original ordered source-name list *before*
touching the coefficient row. This check turns the earlier lookup law
from an external precondition into a consequence of accepted updates.

The model takes a raw Nat index (like Rust's usize) and independently
checks both bounds and the name at that index. The only assumptions
are injective registered names and successful *checked* execution.
No theorem about Rust BTreeMap internals is claimed.
-/

/-- Decode a raw column only when it is in range and refers to the
requested source name in the original ordered declaration list. -/
def checkedIndex {n : Nat} (names : Fin n → Name)
    (raw : Nat) (requested : Name) : Option (Fin n) :=
  if h : raw < n then
    let column : Fin n := ⟨raw, h⟩
    if names column = requested then some column else none
  else none

/-- Every accepted raw location satisfies the lookup correspondence
law, with no assumption whatsoever about where that raw index came
from. In particular a corrupted in-range BTreeMap value refuses. -/
theorem checkedIndex_sound {n : Nat}
    (names : Fin n → Name) (raw : Nat) (requested : Name)
    (column : Fin n)
    (h : checkedIndex names raw requested = some column) :
    names column = requested := by
  by_cases hb : raw < n
  · by_cases hv : names ⟨raw, hb⟩ = requested
    · have hc : (⟨raw, hb⟩ : Fin n) = column := by
        simpa [checkedIndex, hb, hv] using h
      rw [← hc]
      exact hv
    · simp [checkedIndex, hb, hv] at h
  · simp [checkedIndex, hb] at h

/-- The row is left unchanged on a refusal; the Option wrapper
prevents an unchecked raw index from reaching the bit update. -/
def checkedToggle {n : Nat} (names : Fin n → Name)
    (raw : Nat) (requested : Name) (row : Fin n → Bool) :
    Option (Fin n → Bool) :=
  (checkedIndex names raw requested).map (fun index => toggleIndex index row)

/-- An admitted raw lookup + update is precisely the name-based
semantic update. The earlier external hLookup premise has disappeared. -/
theorem checkedToggle_sound {n : Nat}
    (names : Fin n → Name) (hUnique : Function.Injective names)
    (raw : Nat) (requested : Name) (row updated : Fin n → Bool)
    (h : checkedToggle names raw requested row = some updated) :
    updated = toggleName names row requested := by
  unfold checkedToggle at h
  cases hc : checkedIndex names raw requested with
  | none => simp [hc] at h
  | some index =>
      have heq : toggleIndex index row = updated := by
        simpa [hc] using h
      rw [← heq]
      exact toggle_index_eq_toggle_name names hUnique row requested
        index (checkedIndex_sound names raw requested index hc)

/-- An arbitrary sequence of raw name/index pairs. A bad lookup
aborts the whole sequence rather than returning a partial success. -/
def checkedReplay {n : Nat} (names : Fin n → Name) :
    List (Name × Nat) → (Fin n → Bool) → Option (Fin n → Bool)
  | [], row => some row
  | (requested, raw) :: rest, row => do
      let updated ← checkedToggle names raw requested row
      checkedReplay names rest updated

/-- Universal exactness of every successfully validated raw
name/index transcript. No assumed correctness law for a BTreeMap
lookup remains; rejected locations simply do not produce a result. -/
theorem checkedReplay_sound {n : Nat}
    (names : Fin n → Name) (hUnique : Function.Injective names)
    (steps : List (Name × Nat)) (initial result : Fin n → Bool)
    (h : checkedReplay names steps initial = some result) :
    result = steps.foldl
      (fun row pair => toggleName names row pair.1) initial := by
  induction steps generalizing initial with
  | nil =>
      simp [checkedReplay] at h
      exact h.symm
  | cons head tail ih =>
      rcases head with ⟨requested, raw⟩
      cases hc : checkedToggle names raw requested initial with
      | none =>
          simp [checkedReplay, hc] at h
      | some updated =>
          have ht : checkedReplay names tail updated = some result := by
            simpa [checkedReplay, hc] using h
          have heq : updated = toggleName names initial requested :=
            checkedToggle_sound names hUnique raw requested initial updated hc
          rw [ih updated ht]
          simp only [List.foldl_cons]
          rw [heq]


/-- Dropping raw candidate indices after checked replay leaves the
same ordered name-occurrence trace. -/
theorem foldl_names_of_pairs {n : Nat}
    (names : Fin n → Name) (steps : List (Name × Nat))
    (initial : Fin n → Bool) :
    steps.foldl (fun row pair => toggleName names row pair.1) initial =
      (steps.map Prod.fst).foldl (toggleName names) initial := by
  induction steps generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨requested, raw⟩
      simp only [List.foldl_cons, List.map_cons]
      exact ih (toggleName names initial requested)

/-- Strongest source-matrix seam in this experiment: for every accepted
trace of arbitrary raw indices and names, each final bit equals the
GF(2) source-occurrence parity at that declared column. The theorem
does not assume the raw map values were correct: the checked admission
step must independently validate each one before success. -/
theorem checked_row_matches_occurrence_parity {n : Nat}
    (names : Fin n → Name) (hUnique : Function.Injective names)
    (steps : List (Name × Nat)) (result : Fin n → Bool)
    (h : checkedReplay names steps (fun _ => false) = some result)
    (column : Fin n) :
    result column =
      (steps.map Prod.fst).foldl
        (fun parity name => parity ^^ decide (name = names column)) false := by
  rw [checkedReplay_sound names hUnique steps (fun _ => false) result h]
  rw [foldl_names_of_pairs names steps (fun _ => false)]
  exact foldl_named_at names (steps.map Prod.fst) (fun _ => false) column

#print axioms IndependentETH.AffineIndexToggle.foldl_names_of_pairs
#print axioms IndependentETH.AffineIndexToggle.checked_row_matches_occurrence_parity

#print axioms IndependentETH.AffineIndexToggle.checkedIndex_sound
#print axioms IndependentETH.AffineIndexToggle.checkedToggle_sound
#print axioms IndependentETH.AffineIndexToggle.checkedReplay_sound

#print axioms IndependentETH.AffineIndexToggle.toggle_index_eq_toggle_name
#print axioms IndependentETH.AffineIndexToggle.foldl_lookup_eq_named
#print axioms IndependentETH.AffineIndexToggle.foldl_named_at
#print axioms IndependentETH.AffineIndexToggle.indexed_matrix_row_correct
#print axioms IndependentETH.AffineIndexToggle.duplicate_index_toggle

end IndependentETH.AffineIndexToggle
