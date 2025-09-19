-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def crossing_sum (matrix : List (List Int)) (row col : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem uniform_matrix_crossing_sum
  (rows cols : Nat)
  (val : Int) 
  (matrix : List (List Int))
  (h_rows : rows > 0)
  (h_cols : cols > 0)
  (h_matrix : matrix.length = rows)
  (h_matrix_cols : ∀ row ∈ matrix, row.length = cols)
  (h_uniform : ∀ i j, i < rows → j < cols → 
    (matrix.get! i).get! j = val) :
  ∀ a b, a < rows → b < cols →
    crossing_sum matrix a b = val * (rows + cols - 1) :=
sorry

theorem crossing_sum_manual_calc
  (matrix : List (List Int))
  (h_non_empty : matrix.length > 0)
  (h_rectangular : ∀ row ∈ matrix, row.length = (matrix.get! 0).length) :
  ∀ a b, a < matrix.length → b < (matrix.get! 0).length →
    crossing_sum matrix a b = 
      (matrix.get! a).foldl (· + ·) 0 + 
      (matrix.foldl (fun sum row => row.get! b + sum) 0) -
      (matrix.get! a).get! b :=
sorry

theorem one_by_one_matrix_crossing_sum
  (matrix : List (List Int))
  (h_size : matrix.length = 1 ∧ (matrix.get! 0).length = 1) :
  crossing_sum matrix 0 0 = (matrix.get! 0).get! 0 :=
sorry
-- </vc-theorems>