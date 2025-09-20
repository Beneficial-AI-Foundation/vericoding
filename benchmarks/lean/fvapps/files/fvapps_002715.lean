-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_no_duplicates (arr : List Int) :
  let result := solve arr
  ∀ x ∈ result, (result.count x = 1) ∧ (x ∈ arr) :=
sorry

theorem solve_preserves_elements (arr : List Int) :
  let result := solve arr 
  ∀ x ∈ arr, x ∈ result ↔ x ∈ arr :=
sorry

theorem solve_edge_cases_empty : 
  solve [] = [] :=
sorry

theorem solve_edge_cases_singleton (x : Int) :
  solve [x] = [x] :=
sorry

theorem solve_edge_cases_two_same (x : Int) :
  solve [x, x] = [x] :=
sorry
-- </vc-theorems>