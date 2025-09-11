-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_workout_paths (n m : Nat) (grid : List (List Nat)) : Nat := sorry

theorem square_grid_symmetry {n : Nat} (h : n ≥ 3) (h2 : n ≤ 10) :
  let grid := List.replicate n (List.replicate n 100)
  solve_workout_paths n n grid = 400 * (n - 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minimal_grid :
  let grid := List.replicate 3 (List.replicate 3 0)
  solve_workout_paths 3 3 grid = 0 := sorry

/-
info: 800
-/
-- #guard_msgs in
-- #eval solve_workout_paths 3 3 [[100, 100, 100], [100, 1, 100], [100, 100, 100]]

/-
info: 16
-/
-- #guard_msgs in
-- #eval solve_workout_paths 3 3 [[3, 1, 2], [3, 2, 0], [2, 3, 2]]

/-
info: 501
-/
-- #guard_msgs in
-- #eval solve_workout_paths 3 3 [[100, 0, 100], [1, 100, 100], [0, 100, 100]]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible