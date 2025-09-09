-- <vc-helpers>
-- </vc-helpers>

def Grid := List (List Nat)

def min_cost_to_valid_path (grid: Grid) : Int :=
  sorry

theorem output_constraints (grid: Grid) :
  let result := min_cost_to_valid_path grid
  result = -1 ∨ result ≥ 0 :=
sorry

theorem single_cell_case (grid: Grid) :
  grid.length = 1 → 
  (grid.head?.map List.head?).isSome →
  min_cost_to_valid_path grid = 0 :=
sorry

theorem size_bound (grid: Grid) (h: grid.length ≥ 2) :
  let result := min_cost_to_valid_path grid
  let n := grid.length
  result = -1 ∨ result < n * n :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_cost_to_valid_path [[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [2, 2, 2, 2]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_cost_to_valid_path [[1, 1, 3], [3, 2, 2], [1, 1, 4]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_cost_to_valid_path [[1, 2], [4, 3]]

-- Apps difficulty: interview
-- Assurance level: unguarded