-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def calculate_time_at_position (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_nonnegative {n k : Nat} (h : k > 0) :
  calculate_time_at_position n k ≥ 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval calculate_time_at_position 0 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval calculate_time_at_position 1 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval calculate_time_at_position 1 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible