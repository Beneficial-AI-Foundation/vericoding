-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiply (n : Int) : Int := sorry

theorem multiply_sign_preservation (n : Int) :
  (multiply n ≥ 0) = (n ≥ 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiply_digit_length_scaling (n : Int) (h : -999999 ≤ n ∧ n ≤ 999999) :
  let digit_count := String.length (toString n.natAbs)
  multiply n = n * (5 ^ digit_count) := sorry

theorem multiply_single_digit (n : Int) (h : -9 ≤ n ∧ n ≤ 9) : 
  multiply n = n * 5 := sorry

theorem multiply_zero_preservation (n : Int) :
  n = 0 → multiply n = 0 := sorry
-- </vc-theorems>