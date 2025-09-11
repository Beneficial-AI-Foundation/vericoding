-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def area_largest_square (r : Float) : Float := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem area_zero : 
  area_largest_square 0 = 0 :=
sorry

/-
info: 50
-/
-- #guard_msgs in
-- #eval area_largest_square 5

/-
info: 98
-/
-- #guard_msgs in
-- #eval area_largest_square 7

/-
info: 5000
-/
-- #guard_msgs in
-- #eval area_largest_square 50
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible