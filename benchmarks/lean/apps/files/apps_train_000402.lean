-- <vc-preamble>
def numRollsToTarget (d f t : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def M := 1000000007

theorem impossible_target (d f t : Nat) :
  (t < d ∨ t > d*f) → numRollsToTarget d f t = 0 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_die_possible (f t : Nat) :
  1 ≤ t ∧ t ≤ f → numRollsToTarget 1 f t = 1 :=
sorry

theorem single_die_impossible (f t : Nat) :
  (t < 1 ∨ t > f) → numRollsToTarget 1 f t = 0 :=
sorry

theorem above_max_target (d f : Nat) :
  numRollsToTarget d f (d*f+1) = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval numRollsToTarget 1 6 3

/-
info: 6
-/
-- #guard_msgs in
-- #eval numRollsToTarget 2 6 7

/-
info: 1
-/
-- #guard_msgs in
-- #eval numRollsToTarget 2 5 10
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible