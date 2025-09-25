-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_polynomial_equal (x : Int) (expected : Int) (poly_str : String) : Bool := sorry

theorem constant_polynomial_true (x : Int) : 
  is_polynomial_equal x 5 "5" = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem constant_polynomial_false (x : Int) :
  is_polynomial_equal x 6 "5" = false := sorry

theorem zero_polynomial :
  is_polynomial_equal 0 0 "0" = true := sorry

theorem linear_polynomial :
  is_polynomial_equal 1 1 "x" = true := sorry

theorem quadratic_polynomial :
  is_polynomial_equal 2 4 "x**2" = true := sorry

theorem negative_quadratic :
  is_polynomial_equal (-1) 1 "x**2" = true := sorry
-- </vc-theorems>