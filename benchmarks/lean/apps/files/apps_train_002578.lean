-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dice_sum_outcomes (n s k : Nat) : Nat := sorry

theorem dice_sum_outcomes_invalid_inputs₁ (s k : Nat) :
  dice_sum_outcomes 0 s k = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dice_sum_outcomes_invalid_inputs₂ (n k : Nat) :
  dice_sum_outcomes n 0 k = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval dice_sum_outcomes 4 6 5

/-
info: 10
-/
-- #guard_msgs in
-- #eval dice_sum_outcomes 3 6 6

/-
info: 27
-/
-- #guard_msgs in
-- #eval dice_sum_outcomes 3 6 10
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible