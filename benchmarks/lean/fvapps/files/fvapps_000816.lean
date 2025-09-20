-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_multiples_of_ten (n : Nat) : Nat := sorry

theorem sum_multiples_non_negative (n : Nat) :
  sum_multiples_of_ten n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_multiples_divisible_by_ten (n : Nat) :
  sum_multiples_of_ten n % 10 = 0 := sorry 

theorem sum_multiples_upper_bound (n : Nat) :
  sum_multiples_of_ten n ≤ (n * n) / 2 := sorry

theorem sum_multiples_monotonic (n : Nat) :
  n ≥ 10 → sum_multiples_of_ten n ≥ sum_multiples_of_ten (n-1) := sorry

theorem sum_multiples_decimal_bracket (n : Nat) :
  sum_multiples_of_ten n = sum_multiples_of_ten (n - n % 10) := sorry

theorem sum_multiples_edge_cases :
  sum_multiples_of_ten 0 = 0 ∧ sum_multiples_of_ten 9 = 0 := sorry
-- </vc-theorems>