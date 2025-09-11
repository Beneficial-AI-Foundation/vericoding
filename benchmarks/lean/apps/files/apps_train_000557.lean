-- <vc-preamble>
def abs (n : Int) : Int :=
  if n ≥ 0 then n else -n
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_fruit_diff (apples oranges gold : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_fruit_diff_nonnegative (apples oranges gold : Nat) :
  min_fruit_diff apples oranges gold ≥ 0 :=
  sorry

theorem min_fruit_diff_bounded (apples oranges gold : Nat) : 
  min_fruit_diff apples oranges gold ≤ (if apples ≥ oranges then apples - oranges else oranges - apples) :=
  sorry

theorem min_fruit_diff_with_enough_gold (apples oranges gold : Nat) :
  gold ≥ (if apples ≥ oranges then apples - oranges else oranges - apples) → 
  min_fruit_diff apples oranges gold ≤ 1 :=
  sorry

theorem min_fruit_diff_equal_fruits (fruit gold : Nat) :
  min_fruit_diff fruit fruit gold = 0 :=
  sorry

theorem min_fruit_diff_no_gold (apples oranges : Nat) :
  min_fruit_diff apples oranges 0 = (if apples ≥ oranges then apples - oranges else oranges - apples) :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_fruit_diff 3 4 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_fruit_diff 5 2 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_fruit_diff 3 4 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible