-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_equal_rows_after_flips (matrix: List (List Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem return_value_bounds
  (matrix: List (List Nat))
  (h_binary: ∀ row ∈ matrix, ∀ x ∈ row, x = 0 ∨ x = 1) :
  1 ≤ max_equal_rows_after_flips matrix ∧ max_equal_rows_after_flips matrix ≤ matrix.length :=
sorry

theorem flipping_preserves_result 
  (matrix: List (List Nat))
  (h_binary: ∀ row ∈ matrix, ∀ x ∈ row, x = 0 ∨ x = 1)
  (flipped := matrix.map (fun row => row.map (fun x => 1 - x))) :
  max_equal_rows_after_flips matrix = max_equal_rows_after_flips flipped :=
sorry

theorem identical_rows_give_count
  (matrix: List (List Nat))
  (h_nonempty: matrix.length > 0)
  (h_binary: ∀ row ∈ matrix, ∀ x ∈ row, x = 0 ∨ x = 1)
  (identical := List.replicate matrix.length (matrix[0]'(by sorry))) :
  max_equal_rows_after_flips identical = matrix.length :=
sorry
-- </vc-theorems>