-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def paperwork (n m : Int) : Int := sorry

theorem paperwork_nonnegative (n m : Int) : 
  paperwork n m ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem paperwork_zero_when_nonpositive (n m : Int) : 
  (n ≤ 0 ∨ m ≤ 0) → paperwork n m = 0 := sorry

theorem paperwork_mul_when_positive (n m : Int) :
  n > 0 ∧ m > 0 → paperwork n m = n * m := sorry

theorem paperwork_zero_nonpositive_n (n m : Int) :
  n ≤ 0 → paperwork n m = 0 := sorry

theorem paperwork_zero_nonpositive_m (n m : Int) :
  m ≤ 0 → paperwork n m = 0 := sorry
-- </vc-theorems>