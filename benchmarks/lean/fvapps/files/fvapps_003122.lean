-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def two_decimal_places (x : Float) : Float := sorry

def abs (x : Float) : Float := 
  if x ≥ 0 then x else -x

-- Theorem for correct truncation at two decimal places
-- </vc-definitions>

-- <vc-theorems>
theorem two_decimal_places_truncates (x : Float) : 
  ¬ x.isNaN → ¬ x.isInf → -1000000 ≤ x → x ≤ 1000000 →
  two_decimal_places x = Float.floor (x * 100) / 100 := sorry 

-- Theorem for sign preservation

theorem two_decimal_places_preserves_sign (x : Float) :
  ¬ x.isNaN → ¬ x.isInf → -1000000 ≤ x → x ≤ 1000000 → 
  0.01 ≤ abs x →
  (0 < two_decimal_places x) = (0 < x) := sorry
-- </vc-theorems>