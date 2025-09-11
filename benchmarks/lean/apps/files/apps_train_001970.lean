-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_min_steps (s : String) : Nat := sorry

theorem count_min_steps_nonnegative (s : String) : 
  count_min_steps s ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_min_steps_bounded (s : String) :
  count_min_steps s < 1000000007 := sorry 

theorem count_min_steps_empty :
  count_min_steps "" = 0 := sorry

theorem count_min_steps_ab :
  count_min_steps "ab" = 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_min_steps "ab"

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_min_steps "aab"

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_min_steps "abbaa"
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible