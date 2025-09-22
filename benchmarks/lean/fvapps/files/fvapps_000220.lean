-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_distinct_subsequences (s t : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_distinct_subsequences_nonnegative (s t : String) :
  count_distinct_subsequences s t ≥ 0 :=
  sorry

theorem empty_pattern_count (s : String) :
  count_distinct_subsequences s "" = 1 :=
  sorry

theorem empty_string_count (t : String) (h : t ≠ "") :
  count_distinct_subsequences "" t = 0 :=
  sorry

theorem self_pattern_count (t : String) :
  count_distinct_subsequences t t = 1 :=
  sorry

theorem filtered_chars_count (s t : String) :
  let filtered_s := s.toList.filter (fun c => t.toList.contains c)
  count_distinct_subsequences s t = count_distinct_subsequences (String.mk filtered_s) t :=
  sorry

theorem shorter_string_zero_count (s t : String) :
  s.length < t.length → count_distinct_subsequences s t = 0 :=
  sorry

theorem concatenation_self_count (s₁ s₂ : String) :
  let t := s₁ ++ s₂
  count_distinct_subsequences t t = 1 :=
  sorry
-- </vc-theorems>