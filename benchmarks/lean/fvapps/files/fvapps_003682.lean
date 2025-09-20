-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def kangaroo (k1 r1 k2 r2 : Int) : Bool := sorry

theorem kangaroo_symmetric (k1 r1 k2 r2 : Int) : 
  kangaroo k1 r1 k2 r2 = kangaroo k2 r2 k1 r1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem kangaroo_same_position_same_speed (k r : Int) :
  kangaroo k r k r = true := sorry

theorem kangaroo_different_position_same_speed (k1 k2 r : Int) :
  kangaroo k1 r k2 r = (k1 = k2) := sorry

theorem kangaroo_faster_behind (k1 k2 r1 r2 : Int) :
  (r1 > r2 ∧ k1 > k2) → kangaroo k1 r1 k2 r2 = false := sorry

theorem kangaroo_faster_behind_symmetric (k1 k2 r1 r2 : Int) :
  (r2 > r1 ∧ k2 > k1) → kangaroo k1 r1 k2 r2 = false := sorry
-- </vc-theorems>