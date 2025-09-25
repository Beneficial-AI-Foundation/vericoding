-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def roots (a b c : Float) : Option Float := sorry

theorem roots_sum_correct (a b c: Float) 
  (h: a ≠ 0) :
  match roots a b c with
  | none => b * b - 4 * a * c < 0 
  | some x => x = -b/(2*a)
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem roots_zero_c (a b : Float)
  (ha: a > 0) :
  roots a b 0 = some (-b/a) := sorry
-- </vc-theorems>