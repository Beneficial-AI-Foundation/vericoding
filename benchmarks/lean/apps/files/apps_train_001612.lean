-- <vc-helpers>
-- </vc-helpers>

def min_falling_path_sum (matrix: List (List Int)) : Int := sorry

-- Single element matrix theorem

theorem single_element_matrix_path_sum (n: Int) (h: n ≥ 1 ∧ n ≤ 10):
  min_falling_path_sum [[n]] = n := sorry

-- 2x2 matrix theorem

theorem two_by_two_matrix_path_sum (matrix: List (List Int))
  (hsize: matrix.length = 2 ∧ ∀ row ∈ matrix, row.length = 2)
  (hbound: ∀ row ∈ matrix, ∀ x ∈ row, -10 ≤ x ∧ x ≤ 10):
  min_falling_path_sum matrix = 
    min 
      (min 
        ((matrix.get! 0).get! 0 + (matrix.get! 1).get! 0)
        ((matrix.get! 0).get! 0 + (matrix.get! 1).get! 1))
      (min
        ((matrix.get! 0).get! 1 + (matrix.get! 1).get! 0)
        ((matrix.get! 0).get! 1 + (matrix.get! 1).get! 1)) := sorry

-- Zero matrix theorem  

theorem zero_matrix_path_sum (n: Nat) (h: 2 ≤ n ∧ n ≤ 5):
  let matrix := List.replicate n (List.replicate n 0)
  min_falling_path_sum matrix = 0 := sorry

/-
info: 13
-/
-- #guard_msgs in
-- #eval min_falling_path_sum [[2, 1, 3], [6, 5, 4], [7, 8, 9]]

/-
info: -59
-/
-- #guard_msgs in
-- #eval min_falling_path_sum arr2

/-
info: -36
-/
-- #guard_msgs in
-- #eval min_falling_path_sum arr3

-- Apps difficulty: interview
-- Assurance level: unguarded