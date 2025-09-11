-- <vc-preamble>
def num_good_splits (s : String) : Nat :=
sorry

def reverse (s : String) : String :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniqueChars (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible