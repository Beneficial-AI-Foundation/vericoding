-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def return_number (n : Int) : Int := sorry

theorem return_number_returns_input (n : Int) : 
  return_number n = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem return_number_nonneg (n : Int) (h : n ≥ 0) : 
  return_number n ≥ 0 ∧ return_number n = n := sorry

theorem return_number_nonpos (n : Int) (h : n ≤ 0) :
  return_number n ≤ 0 ∧ return_number n = n := sorry
-- </vc-theorems>