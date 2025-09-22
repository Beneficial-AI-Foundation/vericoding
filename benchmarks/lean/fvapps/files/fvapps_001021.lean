-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_min_value (n d : Nat) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_smaller_than_input (n d : Nat) (h1 : n > 0) (h2 : d > 0) :
  let (result_n, _) := solve_min_value n d
  result_n ≤ n :=
sorry

theorem result_nonnegative (n d : Nat) (h1 : n > 0) (h2 : d > 0) :
  let (result_n, _) := solve_min_value n d
  result_n ≥ 0 :=
sorry

theorem ops_nonnegative (n d : Nat) (h1 : n > 0) (h2 : d > 0) :
  let (_, result_ops) := solve_min_value n d
  result_ops ≥ 0 :=
sorry

theorem larger_numbers_get_smaller (n : Nat) (h : n > 9) :
  let (result_n, _) := solve_min_value n 1
  result_n < n :=
sorry

theorem function_is_deterministic (n d : Nat) (h1 : n > 0) (h2 : d > 0) :
  solve_min_value n d = solve_min_value n d :=
sorry

theorem one_stays_one :
  (solve_min_value 1 1).1 = 1 :=
sorry

theorem single_digit_not_increase (h : 9 ≥ 1) :
  (solve_min_value 9 1).1 ≤ 9 :=
sorry
-- </vc-theorems>