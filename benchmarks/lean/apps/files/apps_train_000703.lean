-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_snake_kingdom (n: Nat) (k: Nat) (snakes: List (List Nat)) : Int := sorry

-- When there are no snakes, solution is impossible
-- </vc-definitions>

-- <vc-theorems>
theorem empty_snakes_impossible {n k : Nat} (h1: 3 ≤ n) (h2: n ≤ 100) (h3: 1 ≤ k) 
    (h4: k ≤ 10) (h5: k ≤ n) : 
  solve_snake_kingdom n k [] = -1 := sorry

-- When there is only one horizontal snake across the grid, solution is impossible  

theorem horizontal_snake_impossible {n k : Nat} (h1: 3 ≤ n) (h2: n ≤ 100) (h3: 1 ≤ k)
    (h4: k ≤ 10) (h5: k ≤ n) :
  solve_snake_kingdom n k [[1, 1, n, 1]] = -1 := sorry

-- When there is only one vertical snake across the grid, solution is impossible

theorem vertical_snake_impossible {n k : Nat} (h1: 3 ≤ n) (h2: n ≤ 100) (h3: 1 ≤ k)
    (h4: k ≤ 10) (h5: k ≤ n) :
  solve_snake_kingdom n k [[1, 1, 1, n]] = -1 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_snake_kingdom 7 3 [[1, 1, 6, 1], [1, 2, 3, 2], [5, 2, 5, 2], [2, 4, 2, 6], [6, 2, 6, 4], [5, 6, 5, 7], [7, 1, 7, 4]]

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_snake_kingdom 7 3 [[1, 1, 6, 1], [1, 2, 3, 2], [5, 2, 5, 2], [2, 6, 2, 6], [6, 2, 6, 4], [5, 6, 5, 7], [7, 1, 7, 4]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded