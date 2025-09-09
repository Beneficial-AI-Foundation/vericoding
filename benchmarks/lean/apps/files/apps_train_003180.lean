def abs (x : Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def minimum (a x : Int) : Int :=
  sorry

theorem minimum_makes_number_divisible (a x : Int) (h : x ≠ 0) :
  (a + minimum a x) % x = 0 ∨ (a - minimum a x) % x = 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval minimum 9 4

/-
info: 2
-/
-- #guard_msgs in
-- #eval minimum 10 6

/-
info: 0
-/
-- #guard_msgs in
-- #eval minimum 15 5

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible