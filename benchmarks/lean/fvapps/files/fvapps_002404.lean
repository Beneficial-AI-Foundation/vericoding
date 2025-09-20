-- <vc-preamble>
def INT32_MAX : Int := 2^31 - 1

def INT32_MIN : Int := -(2^31)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_integer (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_integer_sign (x : Int) :
  let result := reverse_integer x
  (result = 0) ∨ (result > 0 ∧ x > 0) ∨ (result < 0 ∧ x < 0) :=
sorry

theorem reverse_integer_bounds (x : Int) :
  let result := reverse_integer x
  INT32_MIN ≤ result ∧ result ≤ INT32_MAX :=
sorry

theorem single_digit_numbers (x : Int) :
  0 ≤ x ∧ x ≤ 9 →
  reverse_integer x = x :=
sorry

theorem trailing_zeros (x : Int) :
  x > 0 →
  x % 10 = 0 →
  reverse_integer x < x :=
sorry

theorem int32_bounds (x : Int) :
  INT32_MIN ≤ x ∧ x ≤ INT32_MAX →
  let result := reverse_integer x
  INT32_MIN ≤ result ∧ result ≤ INT32_MAX :=
sorry

theorem overflow_cases :
  reverse_integer 1534236469 = 0 ∧
  reverse_integer (-2147483648) = 0 :=
sorry
-- </vc-theorems>