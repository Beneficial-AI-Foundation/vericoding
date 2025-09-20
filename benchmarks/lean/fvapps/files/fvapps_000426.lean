-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_days_to_eat_oranges (n : Nat) : Nat := sorry 

theorem min_days_positive (n : Nat) (h : n > 0) (h₂ : n ≤ 10000) : 
  let result := min_days_to_eat_oranges n
  result ≥ 0 ∧ result ≤ n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_days_optimal_step (n : Nat) (h : n > 1) (h₂ : n ≤ 100) :
  min_days_to_eat_oranges n ≤ 1 + min 
    (n % 2 + min_days_to_eat_oranges (n / 2))
    (n % 3 + min_days_to_eat_oranges (n / 3)) := sorry

theorem min_days_base_cases :
  min_days_to_eat_oranges 0 = 0 ∧ 
  min_days_to_eat_oranges 1 = 1 := sorry
-- </vc-theorems>