-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_max_sequence_sum (n : Nat) (grid : List (List Int)) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_validity {n : Nat} {grid : List (List Int)} 
  (h1 : n > 0) (h2 : grid.length = n) 
  (h3 : ∀ row ∈ grid, row.length = n)
  (h4 : ∀ row ∈ grid, ∀ x ∈ row, -1000 ≤ x ∧ x ≤ 1000) :
  let result := solve_max_sequence_sum n grid
  if result ≠ -1 then
    (∃ elements : List Int,
      -- Result is sum of found elements
      (∀ i, i < n → elements.length = n) ∧
      -- Elements are strictly decreasing
      (∀ i j, i < j → j < n → elements.get! i > elements.get! j) ∧
      -- Each element comes from corresponding row
      (∀ i, i < n → elements.get! i ∈ grid.get! i) ∧
      -- Result doesn't exceed maximum possible sum
      result = elements.foldl (. + .) 0)
  else True :=
sorry

theorem grid_immutability {n : Nat} {grid : List (List Int)}
  (h1 : n > 0) (h2 : grid.length = n) 
  (h3 : ∀ row ∈ grid, row.length = n) :
  let original := grid
  let _ := solve_max_sequence_sum n grid
  grid = original :=
sorry
-- </vc-theorems>