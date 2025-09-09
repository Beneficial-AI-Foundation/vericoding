def num_good_splits (s : String) : Nat :=
sorry

def reverse (s : String) : String :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def uniqueChars (s : String) : Bool :=
sorry

theorem num_good_splits_bounds (s : String) (h : s.length > 0) :
  num_good_splits s ≤ s.length - 1 ∧ num_good_splits s ≥ 0 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval num_good_splits "aacaba"

/-
info: 1
-/
-- #guard_msgs in
-- #eval num_good_splits "abcd"

/-
info: 4
-/
-- #guard_msgs in
-- #eval num_good_splits "aaaaa"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible