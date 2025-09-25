-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ravel_multi_index {n : Nat} (row_indices col_indices : Vector Nat n) 
    (rows cols : Nat) 
    (h_rows_valid : ∀ i : Fin n, row_indices.get i < rows)
    (h_cols_valid : ∀ i : Fin n, col_indices.get i < cols) : Id (Vector Nat n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ravel_multi_index_spec {n : Nat} (row_indices col_indices : Vector Nat n) 
    (rows cols : Nat) 
    (h_rows_valid : ∀ i : Fin n, row_indices.get i < rows)
    (h_cols_valid : ∀ i : Fin n, col_indices.get i < cols) :
    ⦃⌜∀ i : Fin n, row_indices.get i < rows ∧ col_indices.get i < cols⌝⦄
    ravel_multi_index row_indices col_indices rows cols h_rows_valid h_cols_valid
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = row_indices.get i * cols + col_indices.get i ∧
                              result.get i < rows * cols⌝⦄ := by
  sorry
-- </vc-theorems>