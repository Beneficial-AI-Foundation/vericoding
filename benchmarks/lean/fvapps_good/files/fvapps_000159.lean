-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_common_subsequence (s1 s2 : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>