-- <vc-helpers>
-- </vc-helpers>

def min_changes_for_rgb_substring (n k : Nat) (s : String) : Nat :=
  sorry

-- General properties

theorem min_changes_non_negative (n k : Nat) (s : String) :
  (1 ≤ k) → (k ≤ n) → (s.length = n) → 
  min_changes_for_rgb_substring n k s ≥ 0 :=
  sorry

theorem min_changes_upper_bound (n k : Nat) (s : String) :
  (1 ≤ k) → (k ≤ n) → (s.length = n) →
  min_changes_for_rgb_substring n k s ≤ k :=
  sorry

-- When k equals string length

theorem k_equals_length (s : String) :
  s.length > 0 →
  let n := s.length
  0 ≤ min_changes_for_rgb_substring n n s ∧ 
  min_changes_for_rgb_substring n n s ≤ n :=
  sorry

-- When k equals 1

theorem k_equals_one (n : Nat) (s : String) :
  (s.length = n) →
  min_changes_for_rgb_substring n 1 s ≤ 1 :=
  sorry

-- For string of all same characters

theorem all_same_char (n : Nat) (s : String) :
  n ≥ 3 →
  (s.length = n) →
  (∀ c, c ∈ s.data → c = 'R') →
  min_changes_for_rgb_substring n 3 s > 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_changes_for_rgb_substring 5 2 "BGGGG"

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_changes_for_rgb_substring 5 3 "RBRGR"

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_changes_for_rgb_substring 5 5 "BBBRR"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible