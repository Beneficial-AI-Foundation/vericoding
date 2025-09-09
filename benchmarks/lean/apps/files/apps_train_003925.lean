-- <vc-helpers>
-- </vc-helpers>

def count_correct_characters (s1 s2 : String) : Nat := 
  sorry

theorem different_length_strings_raise_error {s1 s2 : String} : 
  s1.length ≠ s2.length → count_correct_characters s1 s2 = 0 := 
  sorry

theorem identical_strings_return_length {s : String} :
  count_correct_characters s s = s.length := 
  sorry

theorem result_cannot_exceed_length {s1 s2 : String} :
  s1.length = s2.length → count_correct_characters s1 s2 ≤ s1.length :=
  sorry

theorem result_is_symmetric {s1 s2 : String} :
  s1.length = s2.length → count_correct_characters s1 s2 = count_correct_characters s2 s1 :=
  sorry

theorem result_is_nonnegative {s1 s2 : String} :
  s1.length = s2.length → count_correct_characters s1 s2 ≥ 0 := 
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_correct_characters "dog" "car"

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_correct_characters "dog" "cog"

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_correct_characters "dog" "dog"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible