-- <vc-helpers>
-- </vc-helpers>

def solve (arr : List Int) : List Int :=
  sorry

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

/-
info: [4, 6, 3]
-/
-- #guard_msgs in
-- #eval solve [3, 4, 4, 3, 6, 3]

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval solve [1, 2, 1, 2, 1, 2, 3]

/-
info: [4, 5, 2, 1]
-/
-- #guard_msgs in
-- #eval solve [1, 1, 4, 5, 1, 2, 1]

-- Apps difficulty: introductory
-- Assurance level: unguarded