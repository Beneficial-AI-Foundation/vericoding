def longest_arithmetic_subsequence (arr: List Int) (diff: Int) : Nat :=
  sorry

def countOccurrences (xs : List Int) (x : Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def maxOccurrences (xs : List Int) : Nat :=
  sorry

theorem las_length_bounded {arr: List Int} {diff: Int} :
  arr ≠ [] → longest_arithmetic_subsequence arr diff ≤ arr.length :=
sorry

theorem las_non_negative {arr: List Int} {diff: Int} :
  arr ≠ [] → longest_arithmetic_subsequence arr diff ≥ 0 :=
sorry

theorem las_zero_diff {arr: List Int} :
  arr ≠ [] → longest_arithmetic_subsequence arr 0 = maxOccurrences arr :=
sorry

theorem las_reverse_symmetry {arr: List Int} {diff: Int} :
  arr ≠ [] → diff > 0 →
    longest_arithmetic_subsequence arr diff = 
    longest_arithmetic_subsequence arr.reverse (-diff) :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval longest_arithmetic_subsequence [1, 2, 3, 4] 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval longest_arithmetic_subsequence [1, 3, 5, 7] 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval longest_arithmetic_subsequence [1, 5, 7, 8, 5, 3, 4, 2, 1] -2

-- Apps difficulty: interview
-- Assurance level: unguarded