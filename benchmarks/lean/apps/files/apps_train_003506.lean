-- <vc-helpers>
-- </vc-helpers>

def abs (n : Int) : Int := sorry

def make_negative (n : Int) : Int := sorry

theorem make_negative_is_nonpositive (n : Int) : 
  make_negative n ≤ 0 := sorry

theorem make_negative_idempotent (n : Int) (h : n ≤ 0) :
  make_negative (make_negative n) = make_negative n := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible