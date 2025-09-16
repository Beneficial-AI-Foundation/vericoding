-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_string_transformation (s1 s2 : String) : Int := sorry

theorem identical_strings_zero_transforms (s : String) :
  solve_string_transformation s s = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounds {s1 s2 : String} :
  s1.length = s2.length →
  solve_string_transformation s1 s2 ≠ -1 →
  0 ≤ solve_string_transformation s1 s2 ∧ 
  solve_string_transformation s1 s2 ≤ s1.length := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_string_transformation "aab" "bcc"

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_string_transformation "cabc" "abcb"

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_string_transformation "aabd" "cccd"
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible