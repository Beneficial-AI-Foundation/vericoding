-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_arrangements (n : Nat) : Nat :=
sorry

def digit_sum (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem deterministic (n : Nat) :
  sum_arrangements n = sum_arrangements n := by
sorry

theorem multiple_of_digit_sum (n : Nat) (h : n > 0) :
  sum_arrangements n % digit_sum n = 0 := by
sorry

theorem single_digit (n : Nat) (h : n > 0) (h₂ : n < 10) :
  sum_arrangements n = n := by
sorry

theorem positive_output (n : Nat) (h : n > 0) :
  sum_arrangements n > 0 := by
sorry
-- </vc-theorems>