-- <vc-preamble>
def MAX_INT : Int := 2147483647
def MIN_INT : Int := -2147483648
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def divide (dividend : Int) (divisor : Int) : Int := sorry

theorem divide_bounds (dividend divisor : Int) (h : divisor ≠ 0) :
  MIN_INT ≤ divide dividend divisor ∧ divide dividend divisor ≤ MAX_INT := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divide_accuracy (dividend divisor : Int) (h1 : divisor ≠ 0) 
  (h2 : divide dividend divisor ≠ MAX_INT) :
  (divide dividend divisor * divisor - dividend).natAbs < divisor.natAbs := sorry

theorem divide_by_zero (dividend : Int) :
  divide dividend 0 = MAX_INT := sorry 

theorem min_int_overflow :
  divide MIN_INT (-1) = MAX_INT := sorry

theorem divide_sign_positive (dividend divisor : Int) (h : dividend * divisor > 0) :
  divide dividend divisor ≥ 0 := sorry

theorem divide_sign_negative (dividend divisor : Int) 
  (h1 : dividend * divisor < 0) (h2 : divide dividend divisor ≠ MAX_INT) :
  divide dividend divisor ≤ 0 := sorry
-- </vc-theorems>