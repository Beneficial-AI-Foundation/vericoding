-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_prime_grid_puzzle (grid : List Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>