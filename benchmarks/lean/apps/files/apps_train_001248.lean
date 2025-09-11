-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_ray_grid (n m w b : Nat) (w_cells b_cells : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_grid_sum {n m : Nat} (hn : 0 < n) (hm : 0 < m) : 
  solve_ray_grid n m 0 0 [] [] = n * m * (m + 1) / 2 :=
sorry

theorem single_black_cell :
  solve_ray_grid 2 3 0 1 [] [1,2] = 9 :=
sorry

theorem example_case :
  solve_ray_grid 4 4 5 2 [1,3,2,1,3,2,3,3,4,3] [1,4,2,3] = 22 :=
sorry

/-
info: 22
-/
-- #guard_msgs in
-- #eval solve_ray_grid 4 4 5 2 [1, 3, 2, 1, 3, 2, 3, 3, 4, 3] [1, 4, 2, 3]

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_ray_grid 2 2 0 0 [] []

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve_ray_grid 2 3 0 1 [] [1, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible