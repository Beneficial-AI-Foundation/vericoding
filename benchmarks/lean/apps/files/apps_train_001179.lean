-- <vc-preamble>
def calc_max_moves (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isqrt (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_max_moves_non_negative (x : Nat) :
  calc_max_moves x ≥ 0 :=
  sorry

theorem calc_max_moves_monotonic (x : Nat) :
  x > 0 → calc_max_moves x ≥ calc_max_moves (x-1) :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval calc_max_moves 3

/-
info: 5
-/
-- #guard_msgs in
-- #eval calc_max_moves 8

/-
info: 6
-/
-- #guard_msgs in
-- #eval calc_max_moves 9
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible