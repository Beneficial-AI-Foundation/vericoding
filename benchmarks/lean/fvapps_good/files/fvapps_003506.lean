-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (n : Int) : Int := sorry

def make_negative (n : Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem make_negative_is_nonpositive (n : Int) : 
  make_negative n ≤ 0 := sorry

theorem make_negative_idempotent (n : Int) (h : n ≤ 0) :
  make_negative (make_negative n) = make_negative n := sorry
-- </vc-theorems>