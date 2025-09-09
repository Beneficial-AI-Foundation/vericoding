-- <vc-helpers>
-- </vc-helpers>

def count_distinct_subsequences (s t : String) : Nat :=
  sorry

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

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_distinct_subsequences "rabbbit" "rabbit"

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_distinct_subsequences "babgbag" "bag"

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_distinct_subsequences "abc" "abc"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible