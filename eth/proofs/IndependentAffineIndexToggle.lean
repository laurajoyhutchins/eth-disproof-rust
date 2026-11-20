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
  fun col => row col ^^ (name == names col)

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
        parity ^^ (name == names col)) (initial col) := by
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
      (fun parity name => parity ^^ (name == names col))
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

#print axioms IndependentETH.AffineIndexToggle.toggle_index_eq_toggle_name
#print axioms IndependentETH.AffineIndexToggle.foldl_lookup_eq_named
#print axioms IndependentETH.AffineIndexToggle.foldl_named_at
#print axioms IndependentETH.AffineIndexToggle.indexed_matrix_row_correct
#print axioms IndependentETH.AffineIndexToggle.duplicate_index_toggle

end IndependentETH.AffineIndexToggle
