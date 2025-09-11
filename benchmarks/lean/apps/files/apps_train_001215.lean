-- <vc-preamble>
def min_time_for_multiple_of_nine (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digit_sum (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_within_bounds (n : Nat) (h : n > 0) :
  let result := min_time_for_multiple_of_nine n
  result ≥ 0 ∧ result ≤ 8 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_time_for_multiple_of_nine 1989

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_time_for_multiple_of_nine 86236

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_time_for_multiple_of_nine 90210
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible