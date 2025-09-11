-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min (nums: List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_singleton :
  find_min [1] = 1 :=
  sorry

theorem find_min_all_equal :
  find_min [1, 1, 1] = 1 :=
  sorry

theorem find_min_rotated_with_zero :
  find_min [2, 2, 2, 0, 2] = 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_min [1, 3, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_min [2, 2, 2, 0, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_min [4, 5, 6, 7, 0, 1, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible