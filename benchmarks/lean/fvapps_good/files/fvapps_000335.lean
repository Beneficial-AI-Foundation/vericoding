-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_deletion_size (strings : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_deletion_size_single_char (s : String) :
  s.length = 1 → min_deletion_size [s] = 0 := 
  sorry

theorem min_deletion_size_same_chars (s : String) :
  s = "aa" → min_deletion_size [s] = 0 :=
  sorry

theorem min_deletion_size_reverse_chars (s : String) :
  s = "ba" → min_deletion_size [s] = 1 :=
  sorry

theorem min_deletion_size_identical_sorted_strs (s : String) :
  s = "ab" → min_deletion_size [s, s] = 0 :=
  sorry

theorem min_deletion_size_identical_unsorted_strs (s : String) :
  s = "ba" → min_deletion_size [s, s] = 1 :=
  sorry

theorem min_deletion_size_different_sorted_strs :
  min_deletion_size ["abc", "def", "ghi"] = 0 :=
  sorry

theorem min_deletion_size_reverse_sorted_str :
  min_deletion_size ["edcba"] = 4 :=
  sorry

theorem min_deletion_size_complex_case :
  min_deletion_size ["babca", "bbazb"] = 3 :=
  sorry
-- </vc-theorems>