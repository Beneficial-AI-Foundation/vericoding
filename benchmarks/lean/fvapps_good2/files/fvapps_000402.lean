-- <vc-preamble>
def M := 1000000007
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numRollsToTarget (d f t : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem impossible_target (d f t : Nat) :
  (t < d ∨ t > d*f) → numRollsToTarget d f t = 0 :=
sorry

theorem single_die_possible (f t : Nat) :
  1 ≤ t ∧ t ≤ f → numRollsToTarget 1 f t = 1 :=
sorry

theorem single_die_impossible (f t : Nat) :
  (t < 1 ∨ t > f) → numRollsToTarget 1 f t = 0 :=
sorry

theorem above_max_target (d f : Nat) :
  numRollsToTarget d f (d*f+1) = 0 :=
sorry
-- </vc-theorems>