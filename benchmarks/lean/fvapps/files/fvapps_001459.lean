-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_minimum_cost (a₀ b₀ c₀ x y z : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_minimum_cost_output_range 
  (a₀ b₀ c₀ x y z : Nat) 
  (h1 : a₀ ≤ 1000) (h2 : b₀ ≤ 1000) (h3 : c₀ ≤ 1000)
  (h4 : x ≤ 1000) (h5 : y ≤ 1000) (h6 : z ≤ 1000) :
  solve_minimum_cost a₀ b₀ c₀ x y z ≤ 2 :=
sorry

theorem solve_minimum_cost_equal_case
  (a₀ b₀ c₀ x y z : Nat)
  (h1 : a₀ = x) (h2 : b₀ = y) (h3 : c₀ = z) :
  solve_minimum_cost a₀ b₀ c₀ x y z = 0 :=
sorry

theorem solve_minimum_cost_all_zeros
  (a₀ b₀ c₀ x y z : Nat)
  (h1 : a₀ = 0) (h2 : b₀ = 0) (h3 : c₀ = 0)
  (h4 : x = 0) (h5 : y = 0) (h6 : z = 0) :
  solve_minimum_cost a₀ b₀ c₀ x y z = 0 :=
sorry

theorem solve_minimum_cost_zero_to_even
  (h1 : solve_minimum_cost 0 0 0 2 2 2 = 2) :
  solve_minimum_cost 0 0 0 2 2 2 = 2 :=
sorry

theorem solve_minimum_cost_odd_to_zero
  (h1 : solve_minimum_cost 1 1 1 0 0 0 = 2) :
  solve_minimum_cost 1 1 1 0 0 0 = 2 :=
sorry
-- </vc-theorems>