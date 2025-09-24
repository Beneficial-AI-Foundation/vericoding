-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_island (grid : List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem largest_island_properties (grid : List (List Nat)) :
  let result := largest_island grid
  -- Result within bounds
  (result ≥ 0 ∧ result ≤ grid.length * (grid.head?.getD []).length) ∧
  -- All 0s means result is 1
  (grid.all (fun row => row.all (fun cell => cell = 0)) → result = 1) ∧
  -- All 1s means result is grid size
  (grid.all (fun row => row.all (fun cell => cell = 1)) → result = grid.length * (grid.head?.getD []).length)
  := by sorry

theorem largest_island_dimensions (grid : List (List Nat)) :
  largest_island grid ≤ grid.length * (grid.head?.getD []).length := by sorry

theorem largest_island_singleton :
  largest_island [[0]] = 1 ∧ largest_island [[1]] = 1 := by sorry
-- </vc-theorems>