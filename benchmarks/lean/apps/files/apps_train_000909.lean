-- <vc-helpers>
-- </vc-helpers>

def min_turns_to_divisible_by_10 (n : Int) : Int :=
  sorry

theorem divisible_by_10_returns_0 (x : Int) :
  x ≥ 0 → x % 10 = 0 → min_turns_to_divisible_by_10 x = 0 :=
  sorry

theorem divisible_by_5_returns_1 (x : Int) :
  x ≥ 0 → x % 5 = 0 → x % 10 ≠ 0 → min_turns_to_divisible_by_10 x = 1 :=
  sorry 

theorem not_divisible_by_5_returns_neg_1 (x : Int) :
  x ≥ 0 → x % 5 ≠ 0 → min_turns_to_divisible_by_10 x = -1 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_turns_to_divisible_by_10 10

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_turns_to_divisible_by_10 25

/-
info: -1
-/
-- #guard_msgs in
-- #eval min_turns_to_divisible_by_10 1

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible