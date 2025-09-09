def calc_max_moves (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def isqrt (n : Nat) : Nat :=
  sorry

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

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible