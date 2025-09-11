-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_matrix_shifts (n m : Nat) (matrix : List (List Nat)) : Nat := sorry

theorem single_column_sum (n : Nat) (h : n > 0) :
  let matrix := List.map (fun i => [i]) (List.range n)
  solve_matrix_shifts n 1 matrix = (n * (n - 1)) / 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_values_sum (n : Nat) (h : n > 0) :
  let matrix := List.replicate n (List.replicate 4 5)
  solve_matrix_shifts n 4 matrix = 5 * n := sorry

theorem zero_matrix_sum (n : Nat) (h : n > 0) :
  let matrix := List.replicate n (List.replicate 4 0)
  solve_matrix_shifts n 4 matrix = 0 := sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval solve_matrix_shifts 2 3 [[2, 5, 7], [4, 2, 4]]

/-
info: 29
-/
-- #guard_msgs in
-- #eval solve_matrix_shifts 3 6 [[4, 1, 5, 2, 10, 4], [8, 6, 6, 4, 9, 10], [5, 4, 9, 5, 8, 7]]

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_matrix_shifts 4 2 [[1, 1], [2, 1], [1, 2], [2, 2]]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded