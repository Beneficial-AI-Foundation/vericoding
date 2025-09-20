-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiply (x y : Int) : Int := sorry

theorem multiply_commutative (x y : Int) : multiply x y = multiply y x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiply_identity_right (x : Int) : multiply x 1 = x := sorry

theorem multiply_zero_right (x : Int) : multiply x 0 = 0 := sorry

theorem multiply_negative_one (x : Int) : multiply x (-1) = -x := sorry

theorem multiply_distributive (x y z : Int) :
  multiply x (y + z) = multiply x y + multiply x z := sorry

theorem multiply_identity_left (x : Int) : multiply 1 x = x := sorry

theorem multiply_zero_left (x : Int) : multiply 0 x = 0 := sorry
-- </vc-theorems>