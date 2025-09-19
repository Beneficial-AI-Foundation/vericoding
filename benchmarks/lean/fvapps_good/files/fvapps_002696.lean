-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def symmetric_point (p q : List Int) : List Int := sorry

def distance (p q : List Int) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem symmetric_point_involution (p q : List Int) : 
  symmetric_point (symmetric_point p q) q = p := sorry

theorem symmetric_point_preserves_distance (p q : List Int) : 
  distance p q = distance q (symmetric_point p q) := sorry 

theorem symmetric_point_self_center (p : List Int) :
  symmetric_point p p = p := sorry
-- </vc-theorems>