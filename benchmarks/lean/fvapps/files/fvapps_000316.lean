-- <vc-preamble>
def maxDistance (grid : List (List Int)) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rotateGrid (grid : List (List Int)) : List (List Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxDistance_bounds (grid : List (List Int)) : 
  let result := maxDistance grid
  result ≥ -1 ∧ (result ≠ -1 → result ≤ 2 * grid.length) :=
sorry

theorem maxDistance_all_water (grid : List (List Int)) :
  (∀ row ∈ grid, ∀ cell ∈ row, cell = 0) → 
  maxDistance grid = -1 :=
sorry

theorem maxDistance_all_land (grid : List (List Int)) :
  (∀ row ∈ grid, ∀ cell ∈ row, cell = 1) → 
  maxDistance grid = -1 :=
sorry 

theorem maxDistance_rotation {grid : List (List Int)} :
  maxDistance grid = maxDistance (rotateGrid grid) :=
sorry

theorem maxDistance_edge_cases :
  maxDistance [[1]] = -1 ∧
  maxDistance [[0]] = -1 ∧
  maxDistance [[1,0],[0,0]] = 2 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval maxDistance [[1, 0, 1], [0, 0, 0], [1, 0, 1]]

/-
info: 4
-/
-- #guard_msgs in
-- #eval maxDistance [[1, 0, 0], [0, 0, 0], [0, 0, 0]]

/-
info: -1
-/
-- #guard_msgs in
-- #eval maxDistance [[0, 0, 0], [0, 0, 0], [0, 0, 0]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded