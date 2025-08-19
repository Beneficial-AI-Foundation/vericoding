import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def fill_row {T : Type} {cols : Nat} (row : Vector T cols) (val : T) (row_idx : Nat) : Vector T cols :=
  Vector.ofFn (fun j => if row_idx = j.val then val else row.get j)

/-- Fill the main diagonal of a 2D matrix with a specified value -/
def fill_diagonal {T : Type} {rows cols : Nat} (mat : Vector (Vector T cols) rows) (val : T) : 
    Id (Vector (Vector T cols) rows) :=
  Vector.ofFn (fun i => fill_row (mat.get i) val i.val)

-- LLM HELPER
lemma fill_row_diagonal {T : Type} {cols : Nat} (row : Vector T cols) (val : T) (row_idx : Nat) (j : Fin cols) :
    row_idx = j.val → (fill_row row val row_idx).get j = val := by
  intro h
  simp [fill_row, Vector.get_ofFn]
  rw [if_pos h]

-- LLM HELPER
lemma fill_row_non_diagonal {T : Type} {cols : Nat} (row : Vector T cols) (val : T) (row_idx : Nat) (j : Fin cols) :
    row_idx ≠ j.val → (fill_row row val row_idx).get j = row.get j := by
  intro h
  simp [fill_row, Vector.get_ofFn]
  rw [if_neg h]

/-- Specification: fill_diagonal modifies the diagonal entries to the specified value -/
theorem fill_diagonal_spec {T : Type} {rows cols : Nat} (mat : Vector (Vector T cols) rows) (val : T) :
    ⦃⌜True⌝⦄
    fill_diagonal mat val
    ⦃⇓result => ⌜-- Diagonal elements are filled with val
      (∀ i : Fin rows, ∀ j : Fin cols, i.val = j.val → 
        (result.get i).get j = val) ∧
      -- Non-diagonal elements remain unchanged
      (∀ i : Fin rows, ∀ j : Fin cols, i.val ≠ j.val → 
        (result.get i).get j = (mat.get i).get j)⌝⦄ := by
  simp [Triple.pure_spec, fill_diagonal]
  constructor
  · intro i j h
    simp [Vector.get_ofFn]
    exact fill_row_diagonal (mat.get i) val i.val j h
  · intro i j h
    simp [Vector.get_ofFn]
    exact fill_row_non_diagonal (mat.get i) val i.val j h