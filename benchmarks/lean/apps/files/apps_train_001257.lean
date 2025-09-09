-- <vc-helpers>
-- </vc-helpers>

def sorted (s : String) : String := sorry

def largest_digit_rearrangement (n : Nat) : Nat := sorry

theorem not_less_than_input (n : Nat) :
  largest_digit_rearrangement n ≥ n := sorry

theorem rearrangement_idempotent (n : Nat) :
  largest_digit_rearrangement (largest_digit_rearrangement n) = largest_digit_rearrangement n := sorry

theorem preserves_length (n : Nat) :
  (toString (largest_digit_rearrangement n)).length = (toString n).length := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval largest_digit_rearrangement 2

/-
info: 221
-/
-- #guard_msgs in
-- #eval largest_digit_rearrangement 212

/-
info: 4321
-/
-- #guard_msgs in
-- #eval largest_digit_rearrangement 4321

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible