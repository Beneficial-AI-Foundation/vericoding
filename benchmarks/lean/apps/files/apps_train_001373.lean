-- <vc-helpers>
-- </vc-helpers>

def praneet_algorithm (n : Nat) (a : Nat) : Nat :=
  sorry

theorem praneet_algorithm_non_negative (n : Nat) (a : Nat) :
  praneet_algorithm n a ≥ 0 := sorry

theorem praneet_algorithm_upper_bound (n : Nat) (a : Nat) :
  praneet_algorithm n a ≤ n := sorry

theorem praneet_algorithm_zero_iterations (n : Nat) :
  praneet_algorithm n 0 = n := sorry 

theorem praneet_algorithm_composable (n : Nat) :
  praneet_algorithm n 2 = praneet_algorithm (praneet_algorithm n 1) 1 := sorry

theorem praneet_algorithm_divisible_by_10 (n : Nat) :
  praneet_algorithm (n * 10) 1 = n := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible