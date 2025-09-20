-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def super_pow (base : Int) (exponent_digits : List Int) : Int :=
  sorry

def pow_mod (base exp m : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem super_pow_range (base : Int) (exp_digits : List Int)
  (h1 : base > 0)
  (h2 : exp_digits.length > 0)
  (h3 : exp_digits.length ≤ 10)
  (h4 : ∀ d ∈ exp_digits, 0 ≤ d ∧ d ≤ 9) :
  let result := super_pow base exp_digits
  0 ≤ result ∧ result < 1337 :=
sorry

theorem super_pow_small_exp (base : Int) (exp_digit : Int)
  (h1 : base > 0)
  (h2 : 0 ≤ exp_digit)
  (h3 : exp_digit < 5) :
  super_pow base [exp_digit] = pow_mod base exp_digit 1337 :=
sorry

theorem super_pow_zero (base : Int)
  (h : base > 0) :
  super_pow base [0] = 1 :=
sorry

theorem super_pow_one (base : Int) (exp_digits : List Int)
  (h1 : exp_digits.length > 0)
  (h2 : exp_digits.length ≤ 5)
  (h3 : ∀ d ∈ exp_digits, 0 ≤ d ∧ d ≤ 9) :
  super_pow 1 exp_digits = 1 :=
sorry
-- </vc-theorems>