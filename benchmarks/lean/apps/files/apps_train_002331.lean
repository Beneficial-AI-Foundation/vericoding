-- <vc-helpers>
-- </vc-helpers>

def find_longest_harmonious_subsequence (nums : List Int) : Nat :=
  sorry

theorem find_longest_harmonious_subsequence_non_negative (nums : List Int) :
  find_longest_harmonious_subsequence nums ≥ 0 :=
sorry

theorem find_longest_harmonious_subsequence_leq_length (nums : List Int) :
  find_longest_harmonious_subsequence nums ≤ nums.length :=
sorry

theorem find_longest_harmonious_subsequence_empty (nums : List Int) :
  nums = [] → find_longest_harmonious_subsequence nums = 0 :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_longest_harmonious_subsequence [1, 3, 2, 2, 5, 2, 3, 7]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_longest_harmonious_subsequence [1, 2, 3, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_longest_harmonious_subsequence [1, 1, 1, 1]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible