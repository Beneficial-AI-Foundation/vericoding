-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def roundToNext5 (n: Int) : Int := sorry

theorem roundToNext5_multiple_of_5 (n: Int) :
  (roundToNext5 n) % 5 = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem roundToNext5_not_less_than_input (n: Int) :
  roundToNext5 n ≥ n := sorry

theorem roundToNext5_is_minimum (n: Int) :
  ∀ x, x < roundToNext5 n → (x % 5 ≠ 0 ∨ x < n) := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval round_to_next5 0

/-
info: 5
-/
-- #guard_msgs in
-- #eval round_to_next5 2

/-
info: 15
-/
-- #guard_msgs in
-- #eval round_to_next5 12

/-
info: 0
-/
-- #guard_msgs in
-- #eval round_to_next5 -2

/-
info: -5
-/
-- #guard_msgs in
-- #eval round_to_next5 -5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded