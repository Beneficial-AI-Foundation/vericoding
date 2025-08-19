import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Convert 2D multi-indices to flat indices using C-style (row-major) ordering.
    
    Takes arrays of row and column indices and converts them to flat indices
    for an array with given dimensions. The conversion uses row-major ordering
    where flat_index = row_index * cols + col_index.
    
    The function requires that all indices are within bounds of the specified dimensions.
-/
def ravel_multi_index {n : Nat} (row_indices col_indices : Vector Nat n) 
    (rows cols : Nat) 
    (h_rows_valid : ∀ i : Fin n, row_indices.get i < rows)
    (h_cols_valid : ∀ i : Fin n, col_indices.get i < cols) : Id (Vector Nat n) :=
  do
    let result := Vector.ofFn (fun i => row_indices.get i * cols + col_indices.get i)
    return result

/-- Specification: ravel_multi_index converts 2D indices to flat indices using row-major ordering.
    
    Precondition: All row and column indices must be within bounds
    Postcondition: Each flat index is computed as row_index * cols + col_index
    
    Mathematical properties:
    1. The flat index correctly represents the 2D position in a flattened array
    2. All resulting indices are within bounds of the flattened array
    3. The conversion preserves the ordering relationship between multi-indices
    
    This specification captures the essential behavior of NumPy's ravel_multi_index
    for the 2D case with C-style ordering. The function maps 2D coordinates to
    their corresponding positions in a flattened representation of the array.
-/
theorem ravel_multi_index_spec {n : Nat} (row_indices col_indices : Vector Nat n) 
    (rows cols : Nat) 
    (h_rows_valid : ∀ i : Fin n, row_indices.get i < rows)
    (h_cols_valid : ∀ i : Fin n, col_indices.get i < cols) :
    ⦃⌜∀ i : Fin n, row_indices.get i < rows ∧ col_indices.get i < cols⌝⦄
    ravel_multi_index row_indices col_indices rows cols h_rows_valid h_cols_valid
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = row_indices.get i * cols + col_indices.get i ∧
                              result.get i < rows * cols⌝⦄ := by
  intro h_pre
  simp [ravel_multi_index]
  constructor
  · intro i
    simp [Vector.get_ofFn]
  · intro i
    simp [Vector.get_ofFn]
    have h_row := h_rows_valid i
    have h_col := h_cols_valid i
    have h1 : row_indices.get i * cols < rows * cols := by
      apply Nat.mul_lt_mul_of_pos_right h_row
      cases' cols with cols
      · simp at h_col
      · simp
    have h2 : col_indices.get i < cols := h_col
    omega