-- <vc-helpers>
-- </vc-helpers>

def min_steps_to_anagram (s1 s2 : String) : Nat :=
  sorry

theorem anagram_non_negative (s1 s2 : String) :
  min_steps_to_anagram s1 s2 ≥ 0 :=
  sorry

theorem empty_strings_zero_steps :
  min_steps_to_anagram "" "" = 0 :=
  sorry

theorem same_string_zero_steps (s : String) :
  min_steps_to_anagram s s = 0 :=
  sorry

theorem anagram_symmetry (s : String) :
  min_steps_to_anagram s s = 0 :=
  sorry

theorem steps_bounded_by_length (s t : String) :
  min_steps_to_anagram s t ≤ t.length :=
  sorry

theorem empty_string_steps :
  min_steps_to_anagram "" "" = 0 ∧
  min_steps_to_anagram "a" "" = 0 ∧
  min_steps_to_anagram "" "a" = 1 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_steps_to_anagram "bab" "aba"

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_steps_to_anagram "leetcode" "practice"

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_steps_to_anagram "anagram" "mangaar"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible