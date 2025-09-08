/-
Given a matrix consisting of 0s and 1s, we may choose any number of columns in the matrix and flip every cell in that column.  Flipping a cell changes the value of that cell from 0 to 1 or from 1 to 0.
Return the maximum number of rows that have all values equal after some number of flips.

Example 1:
Input: [[0,1],[1,1]]
Output: 1
Explanation: After flipping no values, 1 row has all values equal.

Example 2:
Input: [[0,1],[1,0]]
Output: 2
Explanation: After flipping values in the first column, both rows have equal values.

Example 3:
Input: [[0,0,0],[0,0,1],[1,1,0]]
Output: 2
Explanation: After flipping values in the first two columns, the last two rows have equal values.

Note:

1 <= matrix.length <= 300
1 <= matrix[i].length <= 300
All matrix[i].length's are equal
matrix[i][j] is 0 or 1
-/

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