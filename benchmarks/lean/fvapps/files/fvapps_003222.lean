-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def narcissistic (n : Nat) : Bool :=
  sorry

def digit_power_sum (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem narcissistic_returns_bool (n : Nat) :
  ∃ (b : Bool), narcissistic n = b :=
sorry

theorem narcissistic_digit_power_sum (n : Nat) :
  narcissistic n = (n = digit_power_sum n) :=
sorry

theorem known_narcissistic_numbers :
  narcissistic 0 = true ∧
  narcissistic 1 = true ∧
  narcissistic 2 = true ∧
  narcissistic 3 = true ∧
  narcissistic 4 = true ∧
  narcissistic 5 = true ∧
  narcissistic 6 = true ∧
  narcissistic 7 = true ∧
  narcissistic 8 = true ∧
  narcissistic 9 = true ∧
  narcissistic 153 = true ∧
  narcissistic 370 = true ∧
  narcissistic 371 = true ∧
  narcissistic 407 = true :=
sorry
-- </vc-theorems>