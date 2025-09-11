-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_nice_staircases (n : Nat) : Nat := sorry

theorem count_nice_staircases_positive (n : Nat) (h : n > 0):
  count_nice_staircases n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_nice_staircases_bounded (n : Nat):
  count_nice_staircases n ≤ n := sorry

theorem count_nice_staircases_deterministic (n : Nat):
  count_nice_staircases n = count_nice_staircases n := sorry

theorem count_nice_staircases_monotonic (n : Nat) (h : n > 1):
  count_nice_staircases n ≥ count_nice_staircases (n-1) := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_nice_staircases 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_nice_staircases 8

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_nice_staircases 6

/-
info: 30
-/
-- #guard_msgs in
-- #eval count_nice_staircases 1000000000000000000
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible