-- <vc-preamble>
def solve_parking_thief (m n : Nat) (grid : List (List Char)) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def updateList {α} (xs : List α) (i : Nat) (v : α) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_grid_zero (m n : Nat) (h1 : m > 0) (h2 : n > 0) :
  let grid := List.replicate m (List.replicate n 'N')
  solve_parking_thief m n grid = 0 := by
  sorry

theorem single_row_min_distance (m n : Nat) (p_positions : List Nat) 
  (h1 : m > 0) (h2 : n > 0) (h3 : ∀ p ∈ p_positions, p < n) :
  let grid := List.replicate m (List.replicate n 'N')
  let grid_with_p := updateList grid 0 
    (p_positions.foldl (fun row p => updateList row p 'P') (List.replicate n 'N'))
  p_positions ≠ [] →
  solve_parking_thief m n grid_with_p ≥ 
    (List.maximum? p_positions).getD 0 - (List.minimum? p_positions).getD 0 := by
  sorry

theorem single_row_no_p_zero (m n : Nat) (h1 : m > 0) (h2 : n > 0) :
  let grid := List.replicate m (List.replicate n 'N')
  solve_parking_thief m n grid = 0 := by
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve_parking_thief 4 5 [["N", "P", "N", "N", "P"], ["N", "N", "P", "N", "N"], ["N", "P", "N", "N", "N"], ["P", "N", "N", "N", "N"]]

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_parking_thief 3 3 [["N", "P", "P"], ["P", "P", "P"], ["P", "P", "N"]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_parking_thief 2 3 [["N", "N", "N"], ["N", "N", "N"]]
-- </vc-theorems>