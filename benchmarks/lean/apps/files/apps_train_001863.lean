-- <vc-helpers>
-- </vc-helpers>

def max_equal_rows_after_flips (matrix: List (List Nat)) : Nat :=
sorry

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

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_equal_rows_after_flips [[0, 1], [1, 1]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_equal_rows_after_flips [[0, 1], [1, 0]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_equal_rows_after_flips [[0, 0, 0], [0, 0, 1], [1, 1, 0]]

-- Apps difficulty: interview
-- Assurance level: unguarded