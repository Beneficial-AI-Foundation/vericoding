-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def integer_and_float_division (a b : Int) : Option (Int × Float) := sorry

theorem int_div_eq_quotient {a b : Int} (h : b ≠ 0) :
  (integer_and_float_division a b).map (·.1) = some (a / b) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem float_div_eq_quotient {a b : Int} (h : b ≠ 0) :
  (integer_and_float_division a b).map (·.2) = some (Float.ofInt a / Float.ofInt b) := sorry

theorem zero_div_is_none (a : Int) :
  integer_and_float_division a 0 = none := sorry
-- </vc-theorems>