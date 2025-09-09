-- <vc-helpers>
-- </vc-helpers>

def two_decimal_places (x : Float) : Float := sorry

def abs (x : Float) : Float := 
  if x ≥ 0 then x else -x

-- Theorem for correct truncation at two decimal places

theorem two_decimal_places_truncates (x : Float) : 
  ¬ x.isNaN → ¬ x.isInf → -1000000 ≤ x → x ≤ 1000000 →
  two_decimal_places x = Float.floor (x * 100) / 100 := sorry 

-- Theorem for sign preservation

theorem two_decimal_places_preserves_sign (x : Float) :
  ¬ x.isNaN → ¬ x.isInf → -1000000 ≤ x → x ≤ 1000000 → 
  0.01 ≤ abs x →
  (0 < two_decimal_places x) = (0 < x) := sorry

/-
info: 10.12
-/
-- #guard_msgs in
-- #eval two_decimal_places 10.1289767789

/-
info: -7488.83
-/
-- #guard_msgs in
-- #eval two_decimal_places -7488.83485834983

/-
info: 4.65
-/
-- #guard_msgs in
-- #eval two_decimal_places 4.653725356

-- Apps difficulty: introductory
-- Assurance level: unguarded