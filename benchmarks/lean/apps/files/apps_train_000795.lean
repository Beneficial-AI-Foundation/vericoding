-- <vc-helpers>
-- </vc-helpers>

def solve_prime_grid_puzzle (grid : List Nat) : Int :=
  sorry

theorem identity_case (target : List Nat) :
  target = [1,2,3,4,5,6,7,8,9] →
  solve_prime_grid_puzzle target = 0 :=
sorry

theorem six_moves (grid : List Nat) :
  grid = [7,3,2,4,1,5,6,8,9] →
  solve_prime_grid_puzzle grid = 6 :=
sorry

theorem impossible (grid : List Nat) :
  grid = [9,8,5,2,4,1,3,7,6] →
  solve_prime_grid_puzzle grid = -1 :=
sorry

theorem invalid_short (grid : List Nat) :
  grid = [1,2,3] →
  solve_prime_grid_puzzle grid = -1 :=
sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_prime_grid_puzzle [7, 3, 2, 4, 1, 5, 6, 8, 9]

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_prime_grid_puzzle [9, 8, 5, 2, 4, 1, 3, 7, 6]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_prime_grid_puzzle [1, 2, 3, 4, 5, 6, 7, 8, 9]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible