-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_time_to_eat_bananas (n : Nat) : Nat := sorry

theorem min_time_always_positive (n : Nat) (h : n > 0) : 
  min_time_to_eat_bananas n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_time_monotonic (n : Nat) (h : n > 0) :
  min_time_to_eat_bananas n ≤ min_time_to_eat_bananas (n + 1) := sorry

theorem min_time_upper_bound (n : Nat) (h : n > 0) :
  min_time_to_eat_bananas n ≤ 2 * n := sorry

theorem min_time_small_inputs_1 :
  min_time_to_eat_bananas 1 = 1 := sorry

theorem min_time_small_inputs_2 :
  min_time_to_eat_bananas 2 = 2 := sorry
-- </vc-theorems>