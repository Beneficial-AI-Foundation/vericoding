-- <vc-helpers>
-- </vc-helpers>

def count_squares (n : Int) : Int := sorry

theorem count_squares_zero :
  count_squares 0 = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_squares 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_squares 2

/-
info: 14
-/
-- #guard_msgs in
-- #eval count_squares 3

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible