-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def score (n : Nat) : Nat := sorry

theorem score_non_negative (n : Nat) : score n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem score_monotonic (n : Nat) : 
  n > 0 → score n ≥ score (n-1) := sorry

theorem score_bit_properties (n : Nat) :
  n > 0 → score n = 2^(Nat.log2 (score n) + 1) - 1 := sorry

theorem score_zero : score 0 = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval score 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval score 1

/-
info: 63
-/
-- #guard_msgs in
-- #eval score 49

/-
info: 1048575
-/
-- #guard_msgs in
-- #eval score 1000000
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible