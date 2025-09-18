-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_falling_path_sum (matrix: List (List Int)) : Int := sorry

-- Single element matrix theorem
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>