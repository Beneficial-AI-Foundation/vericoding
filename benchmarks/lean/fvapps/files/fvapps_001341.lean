-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_sum (x y : Int) : Int := sorry

theorem calc_sum_commutative (x y : Int) : 
  calc_sum x y = calc_sum y x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_sum_identity (x : Int) :
  calc_sum x 0 = x := sorry

theorem calc_sum_associative (x y : Int) :
  calc_sum x y = x + y := sorry

theorem calc_sum_inverse (x : Int) :
  calc_sum x (-x) = 0 := sorry
-- </vc-theorems>