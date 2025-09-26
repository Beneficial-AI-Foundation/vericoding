-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_longest_common_pattern (s1 s2 : List Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem symmetric_property (s1 s2 : List Char) :
  find_longest_common_pattern s1 s2 = find_longest_common_pattern s2 s1 := by
  sorry

theorem self_property (s : List Char) :
  find_longest_common_pattern s s = s.length := by
  sorry

theorem length_bounds (s1 s2 : List Char) :
  find_longest_common_pattern s1 s2 ≤ min s1.length s2.length := by
  sorry

theorem non_negative (s1 s2 : List Char) :
  0 ≤ find_longest_common_pattern s1 s2 := by
  sorry

theorem substring_property (s1 s2 s3 : List Char) :
  find_longest_common_pattern s1 s2 ≤ 
  find_longest_common_pattern (s1 ++ s3) (s2 ++ s3) := by
  sorry

theorem empty_string_property (s : List Char) :
  find_longest_common_pattern ([] : List Char) s = 0 ∧
  find_longest_common_pattern s ([] : List Char) = 0 := by
  sorry

theorem repetition_property (s : List Char) (n : Nat) :
  find_longest_common_pattern (List.replicate n s).join (List.replicate n s).join =
  find_longest_common_pattern s s * n := by
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_longest_common_pattern "abcd" "xyz"

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_longest_common_pattern "abcd" "bcda"

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_longest_common_pattern "Codechef" "elfedcc"
-- </vc-theorems>