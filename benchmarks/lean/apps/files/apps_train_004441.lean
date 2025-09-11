-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_squares (n : Int) : Int := sorry

theorem count_squares_zero :
  count_squares 0 = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible