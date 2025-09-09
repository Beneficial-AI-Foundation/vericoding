-- <vc-helpers>
-- </vc-helpers>

def roots (a b c : Float) : Option Float := sorry

theorem roots_sum_correct (a b c: Float) 
  (h: a ≠ 0) :
  match roots a b c with
  | none => b * b - 4 * a * c < 0 
  | some x => x = -b/(2*a)
  := sorry

theorem roots_zero_c (a b : Float)
  (ha: a > 0) :
  roots a b 0 = some (-b/a) := sorry

/-
info: 35
-/
-- #guard_msgs in
-- #eval roots 1 -35 -23

/-
info: 0
-/
-- #guard_msgs in
-- #eval roots 6 0 -24

/-
info: None
-/
-- #guard_msgs in
-- #eval roots 1 6 10

-- Apps difficulty: introductory
-- Assurance level: unguarded