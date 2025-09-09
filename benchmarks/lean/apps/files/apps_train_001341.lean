-- <vc-helpers>
-- </vc-helpers>

def calc_sum (x y : Int) : Int := sorry

theorem calc_sum_commutative (x y : Int) : 
  calc_sum x y = calc_sum y x := sorry

theorem calc_sum_identity (x : Int) :
  calc_sum x 0 = x := sorry

theorem calc_sum_associative (x y : Int) :
  calc_sum x y = x + y := sorry

theorem calc_sum_inverse (x : Int) :
  calc_sum x (-x) = 0 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible