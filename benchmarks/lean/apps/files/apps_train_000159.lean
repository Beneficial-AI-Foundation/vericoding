-- <vc-helpers>
-- </vc-helpers>

def longest_common_subsequence (s1 s2 : String) : Nat :=
  sorry

theorem lcs_length_bounded (s1 s2 : String) :
  longest_common_subsequence s1 s2 ≤ s1.length ∧ 
  longest_common_subsequence s1 s2 ≤ s2.length :=
  sorry

theorem lcs_empty (s : String) :
  longest_common_subsequence s "" = 0 ∧
  longest_common_subsequence "" s = 0 :=
  sorry

theorem lcs_identical (s : String) :
  longest_common_subsequence s s = s.length :=
  sorry

theorem lcs_symmetric (s1 s2 : String) :
  longest_common_subsequence s1 s2 = longest_common_subsequence s2 s1 :=
  sorry

theorem lcs_substring (s1 s2 s3 : String) :
  longest_common_subsequence (s1 ++ s2) s3 ≥ longest_common_subsequence s1 s3 ∧
  longest_common_subsequence (s1 ++ s2) s3 ≥ longest_common_subsequence s2 s3 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval longest_common_subsequence "abcde" "ace"

/-
info: 3
-/
-- #guard_msgs in
-- #eval longest_common_subsequence "abc" "abc"

/-
info: 0
-/
-- #guard_msgs in
-- #eval longest_common_subsequence "abc" "def"

-- Apps difficulty: interview
-- Assurance level: unguarded