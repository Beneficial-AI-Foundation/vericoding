-- <vc-helpers>
-- </vc-helpers>

def maxIncreaseKeepingSkyline (grid : List (List Nat)) : Nat := sorry

-- A grid with uniform values should have no possible increases

theorem uniform_grid_theorem (n : Nat) (v : Nat) :
  let grid := List.replicate n (List.replicate n v)
  maxIncreaseKeepingSkyline grid = 0 := sorry

-- A grid with values only on diagonal should have non-negative increase

theorem diagonal_grid_theorem (n : Nat) :
  let grid := List.map (fun i => 
    List.map (fun j => if i = j then 1 else 0) (List.range n)
  ) (List.range n)
  maxIncreaseKeepingSkyline grid ≥ 0 := sorry

-- A specific 2x2 example case

theorem example_case_theorem :
  maxIncreaseKeepingSkyline [[1,2], [2,1]] = 2 := sorry

/-
info: 35
-/
-- #guard_msgs in
-- #eval maxIncreaseKeepingSkyline [[3, 0, 8, 4], [2, 4, 5, 7], [9, 2, 6, 3], [0, 3, 1, 0]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval maxIncreaseKeepingSkyline [[5]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval maxIncreaseKeepingSkyline [[1, 2], [2, 1]]

-- Apps difficulty: interview
-- Assurance level: unguarded