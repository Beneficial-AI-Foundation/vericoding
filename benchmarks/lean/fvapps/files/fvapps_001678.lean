-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumDigits (n : Int) : Int := sorry

theorem sum_digits_non_negative (n : Int) :
  sumDigits n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_digits_abs_equal (n : Int) :
  sumDigits n = sumDigits (Int.natAbs n) := sorry

theorem sum_digits_less_than_input (n : Int) :
  Int.natAbs n > 9 → sumDigits n < Int.natAbs n := sorry

-- Note: The last property about matching sum of individual digits
-- would require additional string manipulation and digit conversion definitions,
-- so we'll just state it in terms of natural recursion

theorem sum_digits_equals_digit_sum (n : Int) :
  sumDigits n = sumDigits (n / 10) + n % 10 := sorry
-- </vc-theorems>