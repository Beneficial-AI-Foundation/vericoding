/-
# Task
 You're given a two-dimensional array of integers `matrix`. Your task is to determine the smallest non-negative integer that is not present in this array.

# Input/Output

 - `[input]` 2D integer array `matrix`

  A non-empty rectangular matrix. 

 `1 ≤ matrix.length ≤ 10`

 `1 ≤ matrix[0].length ≤ 10`

 - `[output]` an integer

  The smallest non-negative integer that is not present in matrix.

# Example

 For 

 ```
 matrix = [
 [0, 2],
 [5, 1]]```
 the result should be `3`

 0,1,2,`(3)`...5
-/

-- <vc-helpers>
-- </vc-helpers>

def smallest_integer (matrix : List (List Int)) : Nat :=
  sorry

theorem smallest_integer_result_nonnegative (matrix : List (List Int)) :
  0 ≤ smallest_integer matrix := sorry

theorem smallest_integer_not_in_matrix (matrix : List (List Int)) :
  ¬ (∃ row ∈ matrix, ∃ x ∈ row, x ≥ 0 ∧ x = smallest_integer matrix) := sorry

theorem negative_numbers_ignored (matrix : List (List Int)) :
  smallest_integer matrix = 
  smallest_integer (List.map (λ row => List.map (λ x => if x ≥ 0 then x else -1) row) matrix) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval smallest_integer [[0, 2], [5, 1]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval smallest_integer [[1, 2], [3, 4]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval smallest_integer [[-1, -1], [-1, -1]]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible