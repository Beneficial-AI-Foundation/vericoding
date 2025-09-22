-- <vc-preamble>
def abs (x : Int) : Int := 
  if x ≥ 0 then x else -x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def closestMultiple10 (x : Int) : Int := sorry

theorem result_is_multiple_of_10 (x : Int) :
  (closestMultiple10 x) % 10 = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem closest_multiple_property (x : Int) :
  abs (x - closestMultiple10 x) ≤ abs (x - (closestMultiple10 x + 10)) ∧ 
  abs (x - closestMultiple10 x) ≤ abs (x - (closestMultiple10 x - 10)) := sorry

theorem halfway_rounds_up (x : Int) :
  closestMultiple10 (x * 10 + 5) = ((x * 10 + 5) / 10 + 1) * 10 := sorry

theorem result_within_5 (x : Int) :
  abs (x - closestMultiple10 x) ≤ 5 := sorry
-- </vc-theorems>