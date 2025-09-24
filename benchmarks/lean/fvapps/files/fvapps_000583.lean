-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_last_fibonacci_digit (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_last_fib_digit_range (n: Nat) (h: n ≥ 1) : 
  0 ≤ find_last_fibonacci_digit n ∧ find_last_fibonacci_digit n ≤ 9 :=
sorry

theorem find_last_fib_digit_specific_values : 
  find_last_fibonacci_digit 1 = 0 ∧ 
  find_last_fibonacci_digit 2 = 1 ∧
  find_last_fibonacci_digit 4 = 2 ∧
  find_last_fibonacci_digit 8 = 3 :=
sorry
-- </vc-theorems>