-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def square (x : Int) : Int := sorry

theorem square_nonnegative (x : Int) : square x ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_is_multiplication (x : Int) : square x = x * x := sorry

theorem square_symmetric (x : Int) : square (-x) = square x := sorry

theorem square_monotonic (x : Int) (h : x ≥ 0) : square (x + 1) > square x ∨ x = 0 := sorry
-- </vc-theorems>